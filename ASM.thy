section "Stack Machine and Compilation"

theory ASM imports AExp begin

subsection "Stack Machine"

(* The stack machine instructions. *)
datatype instr =
  LOADI val
| LOAD vname
| ADD
| TIMES

(* The semantics is
   + LOADI n puts the immediate n on top of the sta\<^bold>ck;
   + LOAD x puts the value of x on top of the stack;
   + ADD replaces the first two elements by their sum. *)

type_synonym stack = "val list"
(* The top of the stack is the head of the list. *)

(* An instruction is executed in the context of a state
   and transforms a stack into a new stack. *)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1 (LOADI n) _ stack = Some (n # stack)"
| "exec1 (LOAD x) s stack = Some ((s x) # stack)"
| "exec1 ADD _ (j # i # stack) = Some ((i + j) # stack)"
| "exec1 TIMES _ (j # i # stack) = Some((i * j) # stack)"
(* Stack underflow *)
| "exec1 ADD _ [] = None"
| "exec1 ADD _ [_] = None"
| "exec1 TIMES _ [] = None"
| "exec1 TIMES _ [_] = None"

(* A list of instructions is executed one by one. *)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec [] _ stack = Some stack"
| "exec (i # rest) s stack = (case (exec1 i s stack) of
                                None \<Rightarrow> None \<comment> \<open>Stack underflow\<close>
                              | Some stack' \<Rightarrow> exec rest s stack')"

lemma "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]
       = Some [48, 50]"
by simp

subsection "Compilation"

(* Compilation of arithmetic expressions: *)
fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"
| "comp (Times e1 e2) = comp e1 @ comp e2 @ [TIMES]"

lemma "comp (Plus (Plus (V ''x'') (N 42)) (V ''z''))
       = [LOAD ''x'', LOADI 42, ADD, LOAD ''z'', ADD]"
by simp

lemma [simp]: "exec instr1 state stack = Some stack'
               \<Longrightarrow> exec (instr1 @ instr2) state stack
               = exec instr2 state stack'"
by (induction instr1 arbitrary: stack, auto split: option.split)

(* The correctness statement says that executing a compiled expression
   is the same as putting the value of the expression on the stack. *)
theorem exec_comp: "exec (comp a) state stack = Some (aval a state # stack)"
by (induction a arbitrary: stack, auto)

(* Exercise 3.11 *)
type_synonym reg = nat

datatype instr0 =
  LDI int reg
| LD vname reg
| ADD reg reg (* [ADD r1 r2] adds register [r1] to [r2] into [r2] *)
| MUL reg reg (* [MUL r1 r2] multiplies register [r1] by [r2] into [r2] *)

fun exec10 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> val) \<Rightarrow> reg \<Rightarrow> val" where
  "exec10 (LDI n r) _ regfile = regfile (r := n)"
| "exec10 (LD x r) state regfile = regfile (r := state x)"
| "exec10 (ADD r1 r2) _ regfile = regfile (r2 := regfile r1 + regfile r2)"
| "exec10 (MUL r1 r2) _ regfile = regfile (r2 := regfile r1 * regfile r2)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> val) \<Rightarrow> reg \<Rightarrow> val" where
  "exec0 [] _ regfile = regfile"
| "exec0 (instr # rest) state regfile
                                = exec0 rest state (exec10 instr state regfile)"

(* The compiler in this exercise takes an arithmetic expression [a] and a
   register [r] and produces a list of instructions whose execution places
   the value of [a] into [r].

   The registers [> r] should be used in a stack-like fashion for intermediate
   results. The ones[< r] should be left alone. *)

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
  "comp0 (N n) r = [LDI n r]"
| "comp0 (V x) r = [LD x r]"
| "comp0 (Plus e1 e2) r = comp0 e1 r @ comp0 e2 (r+1) @ [ADD (r + 1) r]"
| "comp0 (Times e1 e2) r = comp0 e1 r @ comp0 e2 (r+1) @ [MUL (r + 1) r]"

lemma "comp0 (N 0) 42 = [LDI 0 42]" by simp
value "comp0 (Plus (N 2) (Times (N 2) (N 20))) 32"

(* Compute value 42 in register 32. *)
lemma "(exec0 (comp0 (Plus (N 2) (Times (N 2) (N 20))) 32) <> (\<lambda>_. 0)) 32
       = 42"
by simp

lemma exec_append: "exec0 (xs @ ys) s rs = exec0 ys s (exec0 xs s rs)"
by (induction xs arbitrary: rs, auto)

(* Executing a program in register [q] does not change registers [< q]. *)
lemma exec_unchanged_regs: "r < q \<Longrightarrow> exec0 (comp0 a q) s rs r = rs r"
by (induction a arbitrary: rs r q, auto simp: exec_append)

theorem comp0_correct: "exec0 (comp0 a r) s rs r = aval a s"
by (induct a arbitrary: rs r, auto simp: exec_append exec_unchanged_regs)

end

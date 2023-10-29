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

end

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
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (LOADI n) _ stack = n # stack"
| "exec1 (LOAD x) s stack = (s x) # stack"
| "exec1 ADD _ (j # i # stack) = (i + j) # stack"
| "exec1 TIMES _ (j # i # stack) = (i * j) # stack"

(* A list of instructions is executed one by one. *)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stack = stack"
| "exec (i # rest) s stack = exec rest s (exec1 i s stack)"

lemma "exec [LOADI 5, LOAD ''y'', ADD]
      <''x'' := 42, ''y'' := 43> [50] = [48, 50]" by simp

lemma exec_append [simp]: "exec (is1 @ is2) s stack
                           = exec is2 s (exec is1 s stack)"
by (induct is1 arbitrary: stack, auto)

subsection "Compilation"

(* Compilation of arithmetic expressions: *)
fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"
| "comp (Times e1 e2) = comp e1 @ comp e2 @ [TIMES]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

(* The correctness statement says that executing a compiled expression
   is the same as putting the value of the expression on the stack: *)
theorem exec_comp: "exec (comp a) s stack = aval a s # stack"
by (induction a arbitrary: stack, auto)

end

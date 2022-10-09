section "Stack Machine and Compilation"

theory ASM imports AExp begin

subsection "Stack Machine"

(* The stack machine has three instructions: *)
datatype instr = LOADI val
               | LOAD vname
               | ADD

(* The semantics:
   + LOADI n puts the immediate n on top of the stack,
   + LOAD x puts the value of x on top of the stack, and
   + ADD replaces the two topmost elements by their sum. *)

(* A stack: *)
type_synonym stack = "val list"
(* The top of the stack is the head of the list *)

(* An instruction is executed in the context of a state and transforms a stack into a new stack. *)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (LOADI n) _ stack = n # stack"
| "exec1 (LOAD x) s stack = s x # stack"
| "exec1 ADD _ (j # i # stack) = (i + j) # stack"

(* A list of instructions is executed one by one. *)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stack = stack"
| "exec (i # is) s stack = exec is s (exec1 i s stack)"

value "exec [LOADI 5, LOAD ''y'', ADD]
      <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append [simp]: "exec (is1 @ is2) s stack = exec is2 s (exec is1 s stack)"
apply (induction is1 arbitrary: stack)
apply auto
done

subsection "Compilation"

(* Compilation of arithmetic expressions: *)
fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

(* The correctness statement says that executing a compiled expression
   is the same as putting the value of the expression on the stack: *)
theorem exec_comp: "exec (comp a) s stack = aval a s # stack"
apply (induction a arbitrary: stack)
apply auto
done

end

theory Compiler imports Big_Step Star begin

(* Preliminaries *)

declare [[coercion_enabled]]
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)

(* Hide coercion int applied to length: *)
abbreviation (output) "isize xs \<equiv> int (length xs)"
notation isize ("size")

(* The machine itself *)
(* Realistically, we would map variable names to memory locations. *)

datatype instr =
  LOADI int
| LOAD vname
| ADD
| STORE vname
| JMP int
| JMPLESS int (* Compare two topmost stack elements and jump if
                 the second one is less. *)
| JMPGE int   (* Compare two topmost stack elements and jump if
                 the second one is greater or equal. *)



end

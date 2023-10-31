theory Exercise_3_9 imports BExp begin

(* Exercise 3.9 *)
datatype pbexp =
  Var vname
| Neg pbexp
| And pbexp pbexp
| Or pbexp pbexp

(* For the purely boolean expressions,
   variables range over values of type bool. *)
fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (Var x) s = s x"
| "pbval (Neg b) s = (\<not> pbval b s)"
| "pbval (And b1 b2) s = (pbval b1 s \<and> pbval b2 s)"
| "pbval (Or b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

(* NNF: Negation Normal Form
   Negation is only applied directly to variables. *)
fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (Var _) = True"
| "is_nnf (Neg (Var _)) = True"
| "is_nnf (Neg _) = False"
| "is_nnf (And e1 e2) = (is_nnf e1 \<and> is_nnf e2)"
| "is_nnf (Or e1 e2) = (is_nnf e1 \<and> is_nnf e2)"

(* Convert pbexp into NNF. *)
fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (Var x) = Var x"
| "nnf (And e1 e2) = And (nnf e1) (nnf e2)"
| "nnf (Or e1 e2) = Or (nnf e1) (nnf e2)"
| "nnf (Neg (Var x)) = Neg (Var x)"
| "nnf (Neg (Neg b)) = nnf b"
| "nnf (Neg (And e1 e2)) = Or (nnf (Neg e1)) (nnf (Neg e2))"
| "nnf (Neg (Or e1 e2)) = And (nnf (Neg e1)) (nnf (Neg e2))"

thm nnf.induct

lemma "is_nnf (nnf b)"
  by (induction b rule: nnf.induct, auto)

lemma "pbval (nnf b) s = pbval b s"
  by (induction b rule: nnf.induct, auto)

end

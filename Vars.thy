theory Vars imports Com begin

class vars =
  fixes vars :: "'a \<Rightarrow> vname set"

instantiation aexp :: vars begin
  fun vars_aexp :: "aexp \<Rightarrow> vname set" where
    "vars (N n) = {}"
  | "vars (V x) = {x}"
  | "vars (Plus a\<^sub>1 a\<^sub>2) = vars a\<^sub>1 \<union> vars a\<^sub>2"

  instance ..
end

value "vars (Plus (V ''x'') (V ''y''))"

instantiation bexp :: vars begin
  fun vars_bexp :: "bexp \<Rightarrow> vname set" where
    "vars (Bc v) = {}"
  | "vars (Not b) = vars b"
  | "vars (And b\<^sub>1 b\<^sub>2) = vars b\<^sub>1 \<union> vars b\<^sub>2"
  | "vars (Less a\<^sub>1 a\<^sub>2) = vars a\<^sub>1 \<union> vars a\<^sub>2"

  instance ..
end

value "vars (Less (Plus (V ''z'') (V ''y'')) (V ''x''))"

abbreviation eq_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
("(_ =/ _/ on _)" [50, 0, 50] 50) where
"f = g on X \<equiv> \<forall> x \<in> X. f x = g x"

(* Evaluations of an arithmetic expression in two states equal on the
   initialised variables are equal. *)
lemma aval_eq_if_eq_on_vars [simp]:
  "s\<^sub>1 = s\<^sub>2 on vars a \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
  apply (induction a)
  apply simp_all
done

(* Same as above, for boolean expressions. *)
lemma bval_eq_if_eq_on_vars:
  "s\<^sub>1 = s\<^sub>2 on vars b \<Longrightarrow> bval b s\<^sub>1 = bval b s\<^sub>2"
proof (induction b)
  case (Less a1 a2)
  hence "aval a1 s\<^sub>1 = aval a1 s\<^sub>2" and "aval a2 s\<^sub>1 = aval a2 s\<^sub>2" by simp_all
  thus ?case by simp
qed simp_all

fun lvars :: "com \<Rightarrow> vname set" where
  "lvars SKIP = {}"
| "lvars (x ::= e) = {x}"
| "lvars (c1;; c2) = lvars c1 \<union> lvars c2"
| "lvars (IF b THEN c1 ELSE c2) = lvars c1 \<union> lvars c2"
| "lvars (WHILE b DO c) = lvars c"

fun rvars :: "com \<Rightarrow> vname set" where
  "rvars SKIP = {}"
| "rvars (x ::= e) = vars e"
| "rvars (c1;; c2) = rvars c1 \<union> rvars c2"
| "rvars (IF b THEN c1 ELSE c2) = vars b \<union> rvars c1 \<union> rvars c2"
| "rvars (WHILE b DO c) = vars b \<union> rvars c"

instantiation com :: vars begin
  definition "vars_com c = lvars c \<union> rvars c"

  instance ..
end

lemma vars_com_simps [simp]:
  "vars SKIP = {}"
  "vars (x ::= e) = {x} \<union> vars e"
  "vars (c1;; c2) = vars c1 \<union> vars c2"
  "vars (IF b THEN c1 ELSE c2) = vars b \<union> vars c1 \<union> vars c2"
  "vars (WHILE b DO c) = vars b \<union> vars c"
by (auto simp: vars_com_def)

lemma finite_avars [simp]: "finite (vars (a::aexp))"
by (induction a) simp_all

lemma finite_bvars [simp]: "finite (vars (b::bexp))"
by (induction b) simp_all

lemma finite_lvars [simp]: "finite (lvars c)"
by (induction c) simp_all

lemma finite_rvars [simp]: "finite (rvars c)"
by (induction c) simp_all

lemma finite_cvars [simp]: "finite (vars (c::com))"
by (simp add: vars_com_def)

end

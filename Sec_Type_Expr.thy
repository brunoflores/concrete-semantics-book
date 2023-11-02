theory Sec_Type_Expr imports Big_Step begin

type_synonym level = nat

class sec =
fixes sec :: "'a \<Rightarrow> nat"

(* For the sake of showing examples, we arbitrarily choose a specific
   function for the mapping from variables to security levels:
   a variable of length n has security level n. *)
instantiation list :: (type)sec begin
  definition "sec (x :: 'a list) = length x"

  instance ..
end

instantiation aexp :: sec begin
  fun sec_aexp :: "aexp \<Rightarrow> level" where
    "sec (N n) = 0"
  | "sec (V x) = sec x"
  | "sec (Plus a\<^sub>1 a\<^sub>2) = max (sec a\<^sub>1) (sec a\<^sub>2)"

  instance ..
end

instantiation bexp :: sec begin
  fun sec_bexp :: "bexp \<Rightarrow> level" where
    "sec (Bc v) = 0"
  | "sec (Not b) = sec b"
  | "sec (And b\<^sub>1 b\<^sub>2) = max (sec b\<^sub>1) (sec b\<^sub>2)"
  | "sec (Less a\<^sub>1 a\<^sub>2) = max (sec a\<^sub>1) (sec a\<^sub>2)"

  instance ..
end

(* Two syntactic abbreviations to talk about states agreeing on
   the value of all variables below a certain security level. *)
abbreviation eq_le :: "state \<Rightarrow> state \<Rightarrow> level \<Rightarrow> bool"
("(_ = _ '(\<le> _'))" [51, 51, 0] 50) where
  "s = s' (\<le> l) \<equiv> (\<forall> x. sec x \<le> l \<longrightarrow> s x = s' x)"

abbreviation eq_less :: "state \<Rightarrow> state \<Rightarrow> level \<Rightarrow> bool"
("(_ = _ '(< _'))" [51, 51, 0] 50) where
  "s = s' (< l) \<equiv> (\<forall> x. sec x < l \<longrightarrow> s x = s' x)"

(* The two abbreviations above make our first two security properties
   simple and automatic.

   The evaluation of an expression e only depends on variables with
   level below or equal to sec e. *)

(* Noninterference for arithmetic expressions *)
lemma aval_eq_if_eq_le:
  "\<lbrakk> s\<^sub>1 = s\<^sub>2 (\<le> l);  sec a \<le> l \<rbrakk> \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
by (induct a) auto

(* Noninterference for boolean expressions *)
lemma bval_eq_if_eq_le:
  "\<lbrakk> s\<^sub>1 = s\<^sub>2 (\<le> l);  sec b \<le> l \<rbrakk> \<Longrightarrow> bval b s\<^sub>1 = bval b s\<^sub>2"
by (induct b) (auto simp add: aval_eq_if_eq_le)

end

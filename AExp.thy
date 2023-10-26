theory AExp imports Main begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(* AST of our language of arithmetic expressions *)
datatype aexp =
  N val
| V vname
| Plus aexp aexp

(* Compute the value of an expression *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) _ = n"
| "aval (V x) s = s x"
| "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* Examples *)
value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 7)"
(* Using the "generic function update" notation *)
value "aval (Plus (N 3) (V ''x'')) ((\<lambda>x. 0) (''x'' := 7))"

(* Syntax magic to write larger states compactly *)
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

(* it allows us to... *)
value "aval (Plus (V ''x'') (N 3)) <''x'' := 7>"

(* Constant Folding *)

(* Constant folding in a bottom-up manner *)
fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n"
| "asimp_const (V x) = V x"
| "asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) of
       (N n1, N n2) \<Rightarrow> N (n1 + n2)
     | (a1', a2') \<Rightarrow> Plus a1' a2')"

lemma "asimp_const (Plus (N 1) (N 2)) = N 3" by simp
lemma "asimp_const (Plus (N 1) (Plus (N 2) (N 3))) = N 6" by simp

(* Correctness meas that [asimp_const] does not change the semantics,
   that is, the value of its argument *)
theorem aval_asimp_const: "aval (asimp_const a) s = aval a s"
proof (induct a)
  case (N x)
  thus ?case by simp
next
  case (V x)
  thus ?case by simp
next
  case (Plus a1 a2)
  thus ?case by (auto split: aexp.split)
qed

(* Eliminate all occurrences of 0 in additions.
   Method: optimised versions of the constructors *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)"
| "plus (N i) a = (if i=0 then a else Plus (N i) a)"
| "plus a (N i) = (if i=0 then a else Plus a (N i))"
| "plus a1 a2 = Plus a1 a2"

thm plus.induct

(* It behaves like Plus under evaluation *)
lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply auto
done

(* Replace plus for Plus in a bottom-up manner *)
fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n"
| "asimp (V x) = V x"
| "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp: "aval (asimp a) s = aval a s"
proof (induct a)
  case (N x)
  thus ?case by simp
next
  case (V x)
  thus ?case by simp
next
  case (Plus a1 a2)
  thus ?case by (simp add: aval_plus)
qed

(* Exercise 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N _) = True"
| "optimal (V _) = True"
| "optimal (Plus (N _) (N _)) = False"
| "optimal (Plus a1 a2) = (case (optimal a1, optimal a2) of
                             (True, True) \<Rightarrow> True
                           | _            \<Rightarrow> False)"

theorem const_folded: "optimal (asimp_const a)"
proof (induct a)
  case (N x)
  thus ?case by simp
next
  case (V x)
  thus ?case by simp
next
  case (Plus a1 a2)
  thus ?case by (auto split: aexp.split)
qed

(* Exercise 3.2 *)
fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp (N n) = N n"
| "full_asimp (V x) = V x"
| "full_asimp (Plus a1 a2) =
    (case (full_asimp a1, full_asimp a2) of
       (N n1, Plus (V x) (N n2)) \<Rightarrow> Plus (V x) (N (n1 + n2))
     | (a1', a2') \<Rightarrow> Plus a1' a2')"

lemma "full_asimp (Plus (N 1) (Plus (V x) (N 2))) = Plus (V x) (N 3)" by simp

theorem full_simplified: "aval (full_asimp a) s = aval a s"
proof (induct a)
  case (N x)
  thus ?case by simp
next
  case (V x)
  thus ?case by simp
next
  case (Plus a1 a2)
  thus ?case by (auto split: aexp.split)
qed

(* Exercise 3.3 *)
\<comment> \<open>[subst x a e] is the result of replacing every occurrence of
    variable [x] by [a] in [e].\<close>
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x' a (N n) = N n"
| "subst x' a (V x) = (if x' = x then a else V x)"
| "subst x' a (Plus a1 a2) = Plus (subst x' a a1) (subst x' a a2)"

lemma "subst ''x1'' (N 3) (Plus (V ''x1'') (V ''y'')) = Plus (N 3) (V ''y'')"
by simp

(* The "substitution lemma" says that we can either substitute first
   and evaluate afterwards or evaluate with an updated state. *)
lemma substitution_lemma: "aval (subst x a e) s = aval e (s (x := aval a s))"
proof (induct e)
  case (N x)
  thus ?case by simp
next
  case (V x)
  thus ?case by simp
next
  case (Plus e1 e2)
  thus ?case by simp
qed

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
proof (induct e)
  case (N x)
  thus ?case by simp
next
  case (V x)
  thus ?case by simp
next
  case (Plus e1 e2)
  thus ?case by simp
qed

end

theory AExp imports Main begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(* AST of our language of arithmetic expressions *)
datatype aexp =
  N val
| V vname
| Plus aexp aexp

thm aexp.split

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

(* Eliminate all occurrences of 0 in additions.
   Method: optimised versions of the constructors *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N n1) (N n2) = N (n1 + n2)"
| "plus (N n) a = (if n=0 then a else Plus (N n) a)"
| "plus a (N n) = (if n=0 then a else Plus a (N n))"
| "plus a1 a2 = Plus a1 a2"

(* It behaves like Plus under evaluation *)
lemma aval_plus[simp]: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply auto
done

(* Replace plus for Plus and times for Times in a bottom-up manner *)
fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n"
| "asimp (V x) = V x"
| "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0))) = V (''x'')" by simp

theorem aval_asimp[simp]: "aval (asimp a) s = aval a s"
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
| "optimal (Plus a1 a2) = (case (optimal a1, optimal a2) of (True, True) \<Rightarrow> True | _ \<Rightarrow> False)"

theorem const_folded: "optimal (asimp a)"
proof (induct a)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  \<comment> \<open>Used to work with (auto split: aexp.split) before adding Times.\<close>
  then show ?case sorry
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
lemma substitution_lemma[simp]: "aval (subst x a e) s = aval e (s (x := aval a s))"
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

(* Exercise 3.5 *)
datatype aexp2 =
  N2 val
| V2 vname
| Plus2 aexp2 aexp2
| Incr2 vname

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> val * state" where
  "aval2 (N2 n) s = (n, s)"
| "aval2 (V2 x) s = (s x, s)"
| "aval2 (Plus2 a1 a2) s = (let (a1', s') = aval2 a1 s in
                            let (a2', s'') = aval2 a2 s' in
                            (a1' + a2', s''))"
| "aval2 (Incr2 x) s = (let n = (s x) in
                        let n' = n + 1 in
                        (n, s (x := n')))"

\<comment> \<open>x++ is a C-like post-increment: we return the value of x,
   then increment x and return that final state.\<close>
lemma "aval2 (Plus2 (N2 2) (Incr2 x)) (\<lambda>x. 2) = (4, (\<lambda>x. 2)(x := 3))" by simp

(* Exercise 3.6 *)
datatype lexp =
  Nl int
| Vl vname
| Plusl lexp lexp
| Let vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
  "lval (Nl n) s = n"
| "lval (Vl x) s = s x"
| "lval (Plusl e1 e2) s = lval e1 s + lval e2 s"
| "lval (Let x e1 e2) s = lval e2 (s (x := lval e1 s))"

lemma "lval (Let ''x'' (Nl 2) (Plusl (Vl ''x'') (Nl 3))) (\<lambda>x. 0) = 5" by simp

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl n) = N n"
| "inline (Vl x) = V x"
| "inline (Plusl e1 e2) = Plus (inline e1) (inline e2)"
| "inline (Let x e1 e2) = subst x (inline e1) (inline e2)"

lemma "inline (Let ''x'' (Nl 2) (Plusl (Vl ''x'') (Nl 3))) = Plus (N 2) (N 3)"
by simp

lemma "aval (inline e) s = lval e s"
by (induct e arbitrary: s) auto

end

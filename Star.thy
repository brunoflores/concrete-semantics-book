theory Star imports Main begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

code_pred star .

(* By definition, star r is reflexive and transitive,
   but we need rule induction to prove: *)
lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
by (induction rule: star.induct, assumption, metis step)

(* Exercise 4.2 *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
  "palindrome []"
| "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

theorem "palindrome xs \<Longrightarrow> (rev xs) = xs"
by (induction xs rule: palindrome.induct, auto)

(* Exercise 4.4 *)
(* Inductive definition of the n-fold iteration of a relation [r]. *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  where
  iter_refl: "iter r 0 x x"
| iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n + 1) x z"

theorem "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
by (induction rule: star.induct, auto intro: iter_refl iter_step)

(* Exercise 4.5 *)
datatype alpha = alpha | beta

inductive S :: "alpha list \<Rightarrow> bool" where
  S_1: "S []"
| S_2: "S w \<Longrightarrow> S (alpha # w @ [beta])"
| S_3: "S w \<Longrightarrow> S x \<Longrightarrow> S (w @ x)"

inductive T :: "alpha list \<Rightarrow> bool" where
  T_1: "T []"
| T_2: "T w \<Longrightarrow> T x \<Longrightarrow> T (w @ [alpha] @ x @ [beta])"

theorem T_implies_S: "T w \<Longrightarrow> S w"
by (induction rule: T.induct, auto intro: S_1 S_2 S_3)

lemma TT: "T w \<Longrightarrow> T x \<Longrightarrow> T (x @ w)"
by (induction rule: T.induct, simp, metis T.simps append.assoc)

theorem S_implies_T: "S w \<Longrightarrow> T w"
  apply(induction rule:S.induct)
  apply(auto intro: T_1 T_2)
  apply(metis T.simps T_1 append.left_neutral append_Cons)
  apply(auto intro: TT)
done

theorem "S w = T w"
by (auto intro: T_implies_S S_implies_T)

(* Exercise 4.6 TODO *)
(* Exercise 4.7 TODO *)

end

theory Star imports Main begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

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

end

theory Star imports Main begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

(* By definition, star r is reflexive and transitive, but we need rule induction to prove: *)

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply (induction rule: star.induct)
apply (assumption)
apply (metis step)
done

end

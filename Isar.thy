theory Isar imports Main begin

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by (auto simp: surj_def)
  thus "False" by blast
qed

lemma
  fixes a b :: int
  assumes "b dvd (a+b)"
  shows "b dvd a"
proof -
  have "\<exists> k'. a = b * k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k-1)" using asm by (simp add: algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

(* A typical proof by case analysis on the form of xs: *)
lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y # ys"
  thus ?thesis by simp
qed

(* Alternative: *)
lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

lemma "\<Sigma> {0..n :: nat} = n * (n+1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

end

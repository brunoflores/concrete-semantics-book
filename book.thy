theory book imports Main begin

fun app' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app' [] ys = ys"
| "app' (x#xs) ys = x # app' xs ys"

fun rev' :: "'a list \<Rightarrow> 'a list" where
  "rev' [] = []"
| "rev' (x#xs) = (rev xs) @ (x#[])"

theorem rev_rev [simp]: "rev (rev xs) = xs" apply (induction xs) by auto

end

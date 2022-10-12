theory YT_tut_1 imports Main begin

value "2 + (2 :: nat)"
value "(2 :: nat) * (5+3)"

lemma "(x :: nat) + y = y + x" by auto

lemma "(x :: nat) + (y + z) = (x + y) + z" by auto

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0"
| "count (x#xs) x' = (if x = x' then Suc (count xs x') else count xs x')"

value "count [1,2,3,0,0] (0::nat)"

theorem "count xs x \<le> length xs"
apply (induction xs) apply auto done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x     = [x]"
| "snoc (x#xs) x' = x # (snoc xs x')"

value "snoc [86, 1] (42::nat)"
lemma "snoc [86, 1] (42::nat) = [86, 1, 42]" by auto

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse []     = []"
| "reverse (x#xs) = snoc (reverse xs) x"

value "reverse [1::nat,2,3,4]"

lemma reverse_snoc: "reverse (snoc ys a) = a # (reverse ys)" apply (induction ys) by auto

theorem "reverse (reverse xs) = xs" apply (induction xs) by (auto simp: reverse_snoc)

end

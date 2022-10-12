theory YT_tut_2 imports Main begin

thm fold.simps

fun list_sum :: "nat list \<Rightarrow> nat" where
  "list_sum [] = 0"
| "list_sum (x#xs) = x + list_sum xs"

value "list_sum [1,2,3]"

definition list_sum' :: "nat list \<Rightarrow> nat" where
  "list_sum' xs = fold (+) xs 0"

value "list_sum' [1,2,3]"

thm list_sum'_def

lemma lemma_aux:  "\<forall>a. fold (+) xs a = list_sum xs + a" apply (induction xs) by auto
lemma "list_sum xs = list_sum' xs" apply (induction xs) by (auto simp: list_sum'_def lemma_aux)

datatype 'a ltree = Leaf 'a | Node "'a ltree" "'a ltree"

fun inorder :: "'a ltree \<Rightarrow> 'a list" where
  "inorder (Leaf x) = [x]"
| "inorder (Node l r) = inorder l @ inorder r"

value "inorder (Node (Node (Leaf (1::nat)) (Leaf 2)) (Leaf 3))"

fun fold_ltree :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a ltree \<Rightarrow> 's \<Rightarrow> 's" where
  "fold_ltree f (Leaf x) a = f x a"
| "fold_ltree f (Node l r) a = fold_ltree f r (fold_ltree f l a)"

value "fold_ltree (+) (Node (Node (Leaf (1::nat)) (Leaf 2)) (Leaf 3)) 0"

lemma "\<forall> a. fold f (inorder t) a = fold_ltree f t a" apply (induction t) by auto

fun mirror :: "'a ltree \<Rightarrow> 'a ltree" where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = (Node (mirror r) (mirror l))"


lemma "inorder (mirror t) = rev (inorder t)" apply (induction t) by auto

fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "shuffles xs [] = [xs]"
| "shuffles [] ys = [ys]"
| "shuffles (x#xs) (y#ys) = map (\<lambda>xs. x#xs) (shuffles xs (y#ys)) @
                            map (\<lambda>ys. y#ys) (shuffles (x#xs) ys)"

thm shuffles.induct

lemma "zs \<in> set (shuffles xs ys) \<Longrightarrow> length zs = length xs + length ys"
  apply (induction xs ys arbitrary: zs rule: shuffles.induct) by auto

end

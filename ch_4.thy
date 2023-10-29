theory ch_4 imports Main begin

(* Exercise 4.1 *)
datatype 'a tree =
  Tip
| Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}"
| "set (Node left a right) = {a} \<union> set left \<union> set right"

value "set ((Node (Node Tip 0 Tip) 1 (Node (Node Tip 2 Tip) 3 Tip)) :: int tree)"

lemma "set (Node (Node Tip 1 Tip) 0 (Node (Node Tip 3 Tip) 2 Tip)) = {3, 2, 1, 0}"
by simp

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True"
| "ord (Node l v r) = ((ord l) \<and> (ord r) \<and> (\<forall>e \<in> set l. e \<le> v) \<and> (\<forall>e \<in> set r. v \<le> e))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins n Tip = Node Tip n Tip"
| "ins n (Node l v r) =
    (if n = v then
        Node l v r
     else if v > n then
        Node (ins n l) v r
     else
        Node l v (ins n r))"

lemma set_correct: "set (ins x t) = {x} \<union> set t"
by (induct t, auto)

theorem ins_correct: "ord t \<Longrightarrow> ord (ins i t)"
by (induct t, auto simp: set_correct)

end

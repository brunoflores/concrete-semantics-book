theory BExp imports AExp begin

datatype bexp =
  Bc bool
| Not bexp
| And bexp bexp
| Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v"
| "bval (Not b) s = (\<not> bval b s)"
| "bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"
| "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

lemma "bval (Less (V ''x'') (Plus (N 3) (V ''y''))) <''x'':= 3, ''y'':= 1>
       = True"
by simp

subsection "Constant Folding"

text "Optimising constructors:"

fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc True) = Bc False"
| "not (Bc False) = Bc True"
| "not b = Not b"

lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
by (induct b rule: not.induct) simp_all

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b"
| "and b (Bc True) = b"
| "and (Bc False) b = Bc False"
| "and b (Bc False) = Bc False"
| "and b1 b2 = And b1 b2"

lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
by (induct b1 b2 rule: and.induct) simp_all

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N n1) (N n2) = Bc(n1 < n2)"
| "less a1 a2 = Less a1 a2"

lemma bval_less[simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
by (induct a1 a2 rule: less.induct) simp_all

text "Overall optimiser:"

(* Bottom-up *)
fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v) = Bc v"
| "bsimp (Not b) = not (bsimp b)"
| "bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)"
| "bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

lemma "bsimp (And (Less (N 0) (N 1)) b) = bsimp b" by simp
lemma "bsimp (And (Less (N 1) (N 0)) (Bc True)) = Bc False" by simp

theorem "bval (bsimp b) s = bval b s"
by (induction b) simp_all

end

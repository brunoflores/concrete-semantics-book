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

(* Exercise 3.7 *)
fun eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "eq a b = and (not (less a b)) (not (less b a))"

fun le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "le a b = not (less b a)"

lemma "bval (eq a1 a2) s = (aval a1 s = aval a2 s)"
by auto

lemma "bval (le a1 a2) s = (aval a1 s \<le> aval a2 s)"
by auto

(* Exercise 3.8 *)
datatype ifexp =
  Bc2 bool
| If ifexp ifexp ifexp
| Less2 aexp aexp

(* It is not the case that both bexp are false: *)
fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "or e1 e2 = not (and (not e1) (not e2))"

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 b) _ = b"
| "ifval (If b e1 e2) s = (if (ifval b s) then ifval e1 s else ifval e2 s)"
| "ifval (Less2 e1 e2) s = (aval e1 s < aval e2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc b) = Bc2 b"
| "b2ifexp (Not e) = If (b2ifexp e) (Bc2 False) (Bc2 True)"
| "b2ifexp (And e1 e2) = If (b2ifexp e1) (b2ifexp e2) (Bc2 False)"
| "b2ifexp (Less a1 a2) = Less2 a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 b) = Bc b"
| "if2bexp (If e1 e2 e3) = or (and (if2bexp e1) (if2bexp e2)) (and (not (if2bexp e1)) (if2bexp e3))"
| "if2bexp (Less2 a1 a2) = Less a1 a2"

(* Prove their correctness: they preserve the value of an expression. *)
lemma "ifval (b2ifexp b) s = bval b s"
  by (induction b, auto)

lemma "bval (if2bexp b) s = ifval b s"
  by (induction b, auto)

(* Exercise 3.9 *)
datatype pbexp =
  Var vname
| Neg pbexp
| And pbexp pbexp
| Or pbexp pbexp

(* For the purely boolean expressions,
   variables range over values of type bool. *)
fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (Var x) s = s x"
| "pbval (Neg b) s = (\<not> pbval b s)"
| "pbval (And b1 b2) s = (pbval b1 s \<and> pbval b2 s)"
| "pbval (Or b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

(* NNF: Negation Normal Form
   Negation is only applied directly to variables. *)
fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (Var _) = True"
| "is_nnf (Neg (Var _)) = True"
| "is_nnf (Neg _) = False"
| "is_nnf (And e1 e2) = (is_nnf e1 \<and> is_nnf e2)"
| "is_nnf (Or e1 e2) = (is_nnf e1 \<and> is_nnf e2)"

(* Convert pbexp into NNF. *)
fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (Var x) = Var x"
| "nnf (And e1 e2) = And (nnf e1) (nnf e2)"
| "nnf (Or e1 e2) = Or (nnf e1) (nnf e2)"
| "nnf (Neg (Var x)) = Neg (Var x)"
| "nnf (Neg (Neg b)) = nnf b"
| "nnf (Neg (And e1 e2)) = Or (nnf (Neg e1)) (nnf (Neg e2))"
| "nnf (Neg (Or e1 e2)) = And (nnf (Neg e1)) (nnf (Neg e2))"

thm nnf.induct

lemma "is_nnf (nnf b)"
  by (induction b rule: nnf.induct, auto)

lemma "pbval (nnf b) s = pbval b s"
  by (induction b rule: nnf.induct, auto)

end

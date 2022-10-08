theory AExp imports Main begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s        = n                    " |
"aval (V x) s        = s x                  " |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 7)"
value "aval (Plus (N 3) (V ''x'')) ((\<lambda>x. 0) (''x'' := 7))"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

value "aval (Plus (V ''x'') (N 3)) <''x'' := 7>"

(* Constant Folding *)

(* Constant folding in a bottom-up manner: *)
fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
    (b1, b2) \<Rightarrow> Plus b1 b2)"

(* Correctness meas that asimp_const does not change the semantics,
   that is, the value of its argument: *)
theorem aval_asimp_const:
    "aval (asimp_const a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
done

(* Eliminate all occurrences of 0 in additions.
   Method: optimised versions of the constructors: *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

(* It behaves like Plus under evaluation: *)
lemma aval_plus [simp]:
    "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply auto
done

(* Replace Plus by plus in a bottom-up manner: *)
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp [simp]:
    "aval (asimp a) s = aval a s"
  apply (induction a)
  apply auto
done

end

theory Types imports Star Complex_Main begin

(* We build on \<^theory>\<open>Complex_Main\<close> instead of \<^theory>\<open>Main\<close> to access
the real numbers. *)

datatype val = Iv int | Rv real

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = Ic int | Rc real | V vname | Plus aexp aexp

(* Inductive to express only the cases that make sense and
   leave everything else undefined.

   Our judgement relates an expression and the state is is evaluated in
   to the value it is evaluated to.  *)
inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  "taval (Ic i) _ (Iv i)"
| "taval (Rc r) _ (Rv r)"
| "taval (V x) _ (s x)"
| "taval a\<^sub>1 s (Iv i\<^sub>1) \<Longrightarrow> taval a\<^sub>2 s (Iv i\<^sub>2) \<Longrightarrow>
   taval (Plus a\<^sub>1 a\<^sub>2) s (Iv (i\<^sub>1 + i\<^sub>2))"
| "taval a\<^sub>1 s (Rv r\<^sub>1) \<Longrightarrow> taval a\<^sub>2 s (Rv r\<^sub>2) \<Longrightarrow>
   taval (Plus a\<^sub>1 a\<^sub>2) s (Rv (r\<^sub>1 + r\<^sub>2))"

inductive_cases [elim!]:
  "taval (Ic i) s v"
  "taval (Rc i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"

(* Boolean expressions *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

inductive tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
  "tbval (Bc v) s v"
| "tbval b s bv \<Longrightarrow> tbval (Not b) s (\<not> bv)"
| "tbval b1 s bv1 \<Longrightarrow> tbval b2 s bv2 \<Longrightarrow>
   tbval (And b1 b2) s (bv1 & bv2)"
| "taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2) \<Longrightarrow>
   tbval (Less a1 a2) s (i1 < i2)"
| "taval a1 s (Rv r1) \<Longrightarrow> taval a2 s (Rv r2) \<Longrightarrow>
   tbval (Less a1 a2) s (r1 < r2)"

(* Commands *)

datatype com =
  SKIP
| Assign vname aexp    ("_ ::= _" [1000, 61] 61)
| Seq com  com         ("_;; _"  [60, 61] 60)
| If  bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
| While bexp com       ("WHILE _ DO _"  [0, 61] 61)

(* Small-step semantics of commands *)

inductive small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool"
(infix "\<rightarrow>" 55) where
  Assign:  "taval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))"

| Seq1:   "(SKIP;; c, s) \<rightarrow> (c, s)"
| Seq2:   "(c1, s) \<rightarrow> (c1', s') \<Longrightarrow>
           (c1;; c2, s) \<rightarrow> (c1';; c2, s')"

| IfTrue:  "tbval b s True \<Longrightarrow>
            (IF b THEN c1 ELSE c2, s) \<rightarrow> (c1, s)"
| IfFalse: "tbval b s False \<Longrightarrow>
            (IF b THEN c1 ELSE c2, s) \<rightarrow> (c2, s)"

| While:   "(WHILE b DO c, s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

(* The type system *)



end

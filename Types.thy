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



end

theory Types imports Star Complex_Main begin

(* We build on \<^theory>\<open>Complex_Main\<close> instead of \<^theory>\<open>Main\<close> to access
the real numbers. *)

datatype val = Iv int | Rv real

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = Ic int | Rc real | V vname | Plus aexp aexp



end

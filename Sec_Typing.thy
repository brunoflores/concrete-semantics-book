theory Sec_Typing imports Sec_Type_Expr begin

(* Syntax directed typing *)

(* We write l \<turnstile> c to mean that command c contains no information flows to
   variables lower than level l, and only safe flows to variables \<ge> l. *)
inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile> _)" [0, 0] 50) where
  Skip:   "l \<turnstile> SKIP"
| Assign: "\<lbrakk> sec x \<ge> sec a; sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a"
| Seq:    "\<lbrakk> l \<turnstile> c\<^sub>1; l \<turnstile> c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> c\<^sub>1;; c\<^sub>2"
| If:     "\<lbrakk> max (sec b) l \<turnstile> c\<^sub>1; max (sec b) l \<turnstile> c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
| While:  "max (sec b) l \<turnstile> c \<Longrightarrow> l \<turnstile> WHILE b DO c"

code_pred (expected_modes: i \<Rightarrow> i \<Rightarrow> bool) sec_type .

value "0 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"
value "1 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x''  ::= N 0 ELSE SKIP"
value "2 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^sub>1;;c\<^sub>2"  "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  "l \<turnstile> WHILE b DO c"

(* Anti-monotonicity *)
lemma anti_mono: "\<lbrakk> l \<turnstile> c; l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile> c"
  (* By rule induction on the type system. *)
  apply (induction arbitrary: l' rule: sec_type.induct)
  apply (metis sec_type.intros(1))
  apply (metis le_trans sec_type.intros(2))
  apply (metis sec_type.intros(3))
  apply (metis If le_refl sup_mono sup_nat_def)
  apply (metis While le_refl sup_mono sup_nat_def)
done

(* Confinement: an execution of a command that is type correct
   in context l can only change variables of level l and above. *)
lemma confinement: "\<lbrakk> (c, s) \<Rightarrow> t;  l \<turnstile> c \<rbrakk> \<Longrightarrow> s = t (< l)"
(* By rule induction on the big-step execution. *)
proof (induction rule: big_step_induct)
  case Skip thus ?case by simp
next
  case Assign thus ?case by auto
next
  case Seq thus ?case by auto
next
  case (IfTrue b s c1)
  hence "max (sec b) l \<turnstile> c1" by auto
  hence "l \<turnstile> c1" by (metis max.cobounded2 anti_mono)
  thus ?case using IfTrue.IH by metis
next
  case (IfFalse b s c2)
  hence "max (sec b) l \<turnstile> c2" by auto
  hence "l \<turnstile> c2" by (metis max.cobounded2 anti_mono)
  thus ?case using IfFalse.IH by metis
next
  case WhileFalse thus ?case by auto
next
  case (WhileTrue b s1 c)
  hence "max (sec b) l \<turnstile> c" by auto
  hence "l \<turnstile> c" by (metis max.cobounded2 anti_mono)
  thus ?case using WhileTrue by metis
qed

theorem noninterference:
  "\<lbrakk> (c, s) \<Rightarrow> s'; (c, t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (\<le> l) \<rbrakk> \<Longrightarrow> s' = t' (\<le> l)"
(* By induction on the big-step execution. *)
proof (induction arbitrary: t t' rule: big_step_induct)
  case Skip thus ?case by auto
next
  case (Assign x a s)
  have [simp]: "t' = t(x := aval a t)" using Assign by auto
  have "sec x >= sec a" using \<open>0 \<turnstile> x ::= a\<close> by auto
  show ?case
  proof auto
    assume "sec x \<le> l"
    with \<open>sec x >= sec a\<close> have "sec a \<le> l" by arith
    thus "aval a s = aval a t"
      by (rule aval_eq_if_eq_le[OF \<open>s = t (\<le> l)\<close>])
  next
    fix y assume "y \<noteq> x" "sec y \<le> l"
    thus "s y = t y" using \<open>s = t (\<le> l)\<close> by simp
  qed
next
  case Seq thus ?case by blast
next
  case (IfTrue b s c1 s' c2)
  have "sec b \<turnstile> c1" "sec b \<turnstile> c2" using \<open>0 \<turnstile> IF b THEN c1 ELSE c2\<close> by auto
  show ?case
  proof cases
    assume "sec b \<le> l"
    hence "s = t (\<le> sec b)" using \<open>s = t (\<le> l)\<close> by auto
    hence "bval b t" using \<open>bval b s\<close> by(simp add: bval_eq_if_eq_le)
    with IfTrue.IH IfTrue.prems(1,3) \<open>sec b \<turnstile> c1\<close>  anti_mono
    show ?thesis by auto
  next
    assume "\<not> sec b \<le> l"
    have 1: "sec b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: \<open>sec b \<turnstile> c1\<close> \<open>sec b \<turnstile> c2\<close>)
    from confinement[OF \<open>(c1, s) \<Rightarrow> s'\<close> \<open>sec b \<turnstile> c1\<close>] \<open>\<not> sec b \<le> l\<close>
    have "s = s' (\<le> l)" by auto
    moreover
    from confinement[OF \<open>(IF b THEN c1 ELSE c2, t) \<Rightarrow> t'\<close> 1] \<open>\<not> sec b \<le> l\<close>
    have "t = t' (\<le> l)" by auto
    ultimately show "s' = t' (\<le> l)" using \<open>s = t (\<le> l)\<close> by auto
  qed
next
  case (IfFalse b s c2 s' c1)
  have "sec b \<turnstile> c1" "sec b \<turnstile> c2" using \<open>0 \<turnstile> IF b THEN c1 ELSE c2\<close> by auto
  show ?case
  proof cases
    assume "sec b \<le> l"
    hence "s = t (\<le> sec b)" using \<open>s = t (\<le> l)\<close> by auto
    hence "\<not> bval b t" using \<open>\<not> bval b s\<close> by(simp add: bval_eq_if_eq_le)
    with IfFalse.IH IfFalse.prems(1,3) \<open>sec b \<turnstile> c2\<close> anti_mono
    show ?thesis by auto
  next
    assume "\<not> sec b \<le> l"
    have 1: "sec b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: \<open>sec b \<turnstile> c1\<close> \<open>sec b \<turnstile> c2\<close>)
    from confinement[OF big_step.IfFalse[OF IfFalse(1,2)] 1] \<open>\<not> sec b \<le> l\<close>
    have "s = s' (\<le> l)" by auto
    moreover
    from confinement[OF \<open>(IF b THEN c1 ELSE c2, t) \<Rightarrow> t'\<close> 1] \<open>\<not> sec b \<le> l\<close>
    have "t = t' (\<le> l)" by auto
    ultimately show "s' = t' (\<le> l)" using \<open>s = t (\<le> l)\<close> by auto
  qed
next
  case (WhileFalse b s c)
  have "sec b \<turnstile> c" using WhileFalse.prems(2) by auto
  show ?case
  proof cases
    assume "sec b \<le> l"
    hence "s = t (\<le> sec b)" using \<open>s = t (\<le> l)\<close> by auto
    hence "\<not> bval b t" using \<open>\<not> bval b s\<close> by(simp add: bval_eq_if_eq_le)
    with WhileFalse.prems(1,3) show ?thesis by auto
  next
    assume "\<not> sec b \<le> l"
    have 1: "sec b \<turnstile> WHILE b DO c"
      by(rule sec_type.intros)(simp_all add: \<open>sec b \<turnstile> c\<close>)
    from confinement[OF \<open>(WHILE b DO c, t) \<Rightarrow> t'\<close> 1] \<open>\<not> sec b \<le> l\<close>
    have "t = t' (\<le> l)" by auto
    thus "s = t' (\<le> l)" using \<open>s = t (\<le> l)\<close> by auto
  qed
next
  case (WhileTrue b s1 c s2 s3 t1 t3)
  let ?w = "WHILE b DO c"
  have "sec b \<turnstile> c" using \<open>0 \<turnstile> WHILE b DO c\<close> by auto
  show ?case
  proof cases
    assume "sec b \<le> l"
    hence "s1 = t1 (\<le> sec b)" using \<open>s1 = t1 (\<le> l)\<close> by auto
    hence "bval b t1"
      using \<open>bval b s1\<close> by(simp add: bval_eq_if_eq_le)
    then obtain t2 where "(c,t1) \<Rightarrow> t2" "(?w,t2) \<Rightarrow> t3"
      using \<open>(?w,t1) \<Rightarrow> t3\<close> by auto
    from WhileTrue.IH(2)[OF \<open>(?w,t2) \<Rightarrow> t3\<close> \<open>0 \<turnstile> ?w\<close>
      WhileTrue.IH(1)[OF \<open>(c,t1) \<Rightarrow> t2\<close> anti_mono[OF \<open>sec b \<turnstile> c\<close>]
        \<open>s1 = t1 (\<le> l)\<close>]]
    show ?thesis by simp
  next
    assume "\<not> sec b \<le> l"
    have 1: "sec b \<turnstile> ?w" by(rule sec_type.intros)(simp_all add: \<open>sec b \<turnstile> c\<close>)
    from confinement[OF big_step.WhileTrue[OF WhileTrue.hyps] 1] \<open>\<not> sec b \<le> l\<close>
    have "s1 = s3 (\<le> l)" by auto
    moreover
    from confinement[OF \<open>(WHILE b DO c, t1) \<Rightarrow> t3\<close> 1] \<open>\<not> sec b \<le> l\<close>
    have "t1 = t3 (\<le> l)" by auto
    ultimately show "s3 = t3 (\<le> l)" using \<open>s1 = t1 (\<le> l)\<close> by auto
  qed
qed

end
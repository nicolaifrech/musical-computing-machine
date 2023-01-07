theory Submission
  imports Defs
begin

type_synonym vname = string

(* Arithmetic expressions *)

datatype aexp = N nat | V vname | Plus aexp aexp 

fun aval :: "aexp \<Rightarrow> aexp" where
  "aval (N n) = (N n)" |
  "aval (V v) = (V v)" |
  "aval (Plus e\<^sub>1 e\<^sub>2) = (case (aval e\<^sub>1, aval e\<^sub>2) of
      (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N (n\<^sub>1 + n\<^sub>2) |
      (e\<^sub>1', e\<^sub>2')   \<Rightarrow> Plus e\<^sub>1' e\<^sub>2'
  )"

value "aval (Plus (Plus (N 2) (N 5)) (N 3))"

fun containsVar :: "aexp \<Rightarrow> bool" where
  "containsVar (N _) = False" | 
  "containsVar (V _) = True"  |
  "containsVar (Plus e\<^sub>1 e\<^sub>2) = (containsVar e\<^sub>1 \<or> containsVar e\<^sub>2)"

lemma aval_simp_eq_no_var: "\<not>containsVar e \<longleftrightarrow> (\<exists>n. aval e = N n)"
proof
  assume "\<not> containsVar e"
  then show "\<exists>n. aval e = N n"
  proof(induction e)
  qed auto
next
  assume "\<exists>n. aval e = N n"
  then show "\<not> containsVar e"
  proof(induction e)
  qed(auto split:aexp.splits)
qed

fun subterms :: "aexp \<Rightarrow> aexp set" where
  "subterms (N n) = {N n}" |
  "subterms (V v) = {V v}" |
  "subterms (Plus e\<^sub>1 e\<^sub>2) = {Plus e\<^sub>1 e\<^sub>2} \<union> subterms e\<^sub>1 \<union> subterms e\<^sub>2"

lemma aval_simp_eq_subterm_simp: "(\<exists>n. aval e = N n) \<longleftrightarrow> (\<forall>t \<in> subterms e. \<exists>n. aval t = N n)"
proof
  assume "\<exists>n. aval e = N n"
  then show "\<forall>t\<in>subterms e. \<exists>n. aval t = N n"
  proof(induction e)
    case (Plus e1 e2)
    then show ?case by(fastforce split:aexp.splits)
  qed simp_all
next
  assume "\<forall>t\<in>subterms e. \<exists>n. aval t = N n"
  then show "\<exists>n. aval e = N n"
  proof(induction e)
  qed(auto)
qed

lemma e_is_subterm_e: "e \<in> subterms e" 
  apply(induction e)
  apply(auto)
  done

definition "strict_subterms e = subterms e - {e}"

lemma strict_subt_le_subt: "strict_subterms e \<subset> subterms e"
  using e_is_subterm_e order_less_le strict_subterms_def by auto 

lemma e_does_not_contain_e: "e \<notin> strict_subterms e"
  by (simp add: strict_subterms_def)

(*
lemma "strict_subterms (Plus e\<^sub>1 e\<^sub>2) = subterms e\<^sub>1 \<union> subterms e\<^sub>2"
  apply(induction e\<^sub>1 arbitrary: e\<^sub>2)
  apply(auto simp add: strict_subterms_def)
*)

lemma subt_trans: "f \<in> subterms e \<Longrightarrow> g \<in> subterms f \<Longrightarrow> g \<in> subterms e"
  apply(induction e)
  apply(auto)
  done

(*
lemma "e \<in> subterms f \<and> f \<in> subterms e \<Longrightarrow> e = f"
  apply(induction e arbitrary: f)
  apply(auto)
  apply(metis Un_iff e_is_subterm_e subt_trans subterms.simps(3))
  apply(metis Un_iff e_is_subterm_e subt_trans subterms.simps(3))
  done

lemma aux:"f \<in> subterms e \<Longrightarrow> e \<notin> subterms f \<or> e = f"
  apply(induction e arbitrary: f)
  apply(auto)
  apply(metis Un_iff e_is_subterm_e subt_trans subterms.simps(3))
  apply(metis Un_iff e_is_subterm_e subt_trans subterms.simps(3))
  done

*)

lemma subt_not_parent: "e \<noteq> f \<Longrightarrow> f \<in> subterms e \<Longrightarrow> e \<notin> subterms f"
proof(induction e arbitrary: f)
  case (Plus e1 e2)
  have "f \<in> subterms e1 \<or> f \<in> subterms e2" using Plus.prems(1) Plus.prems(2) by auto 
  then show ?case
  proof(cases "f \<in> subterms e1")
    case True
    then show ?thesis
    proof(cases "f = e1")
      case True
      then show ?thesis using Plus.IH(1) Plus.prems(2) by force 
    next
      case False
      have "e1 \<notin> subterms f" using False Plus.IH(1) True by presburger
      moreover
      have "e1 \<in> subterms (Plus e1 e2)" using e_is_subterm_e by auto
      moreover
      have "(Plus e1 e2) \<notin> subterms f" using calculation(1) calculation(2) subt_trans by blast 
      ultimately
      show ?thesis by blast 
    qed
  next
    case False
    have "f \<in> subterms e2" using False \<open>f \<in> subterms e1 \<or> f \<in> subterms e2\<close> by auto 
    then show ?thesis
    proof(cases "f = e2")
      case True
      then show ?thesis using Plus.IH(2) Plus.prems(2) by force 
    next
      case False
      have "e2 \<notin> subterms f" using False Plus.IH(2) \<open>f \<in> subterms e2\<close> by presburger 
      moreover
      have "e2 \<in> subterms (Plus e1 e2)" using e_is_subterm_e by fastforce 
      moreover
      have "(Plus e1 e2) \<notin> subterms f" using calculation(1) calculation(2) subt_trans by blast 
      ultimately
      show ?thesis by blast 
    qed
  qed
qed simp_all

fun strict_subterms' :: "aexp \<Rightarrow> aexp set" where
  "strict_subterms' (N _) = {}" |
  "strict_subterms' (V _) = {}" |
  "strict_subterms' (Plus e\<^sub>1 e\<^sub>2) = subterms e\<^sub>1 \<union> subterms e\<^sub>2"

lemma strict_subt_eq_strict_subt': "strict_subterms e = strict_subterms' e"
proof(cases e)
  case (Plus e\<^sub>1 e\<^sub>2)
  have "strict_subterms e = subterms e - {e}" using strict_subterms_def by force 
  also have "\<dots> = ({Plus e\<^sub>1 e\<^sub>2} \<union> subterms e\<^sub>1 \<union> subterms e\<^sub>2) - {Plus e\<^sub>1 e\<^sub>2}"
    using Plus subterms.simps(3) by presburger 
  then show ?thesis
    using Plus Un_insert_left subt_not_parent calculation e_is_subterm_e by fastforce 
qed(simp_all add:strict_subterms_def)

corollary strict_subt_of_plus: "strict_subterms (Plus e\<^sub>1 e\<^sub>2) = subterms e\<^sub>1 \<union> subterms e\<^sub>2"
  by (simp add: strict_subt_eq_strict_subt')

fun vars :: "aexp \<Rightarrow> vname set" where
  "vars (N n) = {}" |
  "vars (V v) = {v}" |
  "vars (Plus e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 \<union> vars e\<^sub>2"

(* Assignment *)
(*
type_synonym assignment = "(vname * aexp) list"

fun is_assigned :: "assignment \<Rightarrow> vname \<Rightarrow> bool" where
  "is_assigned [] _ = False" |
  "is_assigned ((v', _)#as) v = (if v' = v then True else is_assigned as v)"

(* partial function *)
fun assigned_val :: "assignment \<Rightarrow> vname \<Rightarrow> aexp" where
  "assigned_val ((v', a)#as) v = (if v' = v then a else assigned_val as v)"

fun assign_new :: "assignment \<Rightarrow> vname \<Rightarrow> aexp \<Rightarrow> assignment" where
  "assign_new [] v a = [(v, a)]" |
  "assign_new ((v',a')#as) v a = (if v' = v then ((v',a')#as) else (v',a')#assign_new as v a)"

fun assign :: "aexp \<Rightarrow> assignment \<Rightarrow> aexp" where
  "assign (N n) _ = N n" |
  "assign (V v) a = (if is_assigned a v then assigned_val a v else V v)" |
  "assign (Plus e\<^sub>1 e\<^sub>2) a = (Plus (assign e\<^sub>1 a) (assign e\<^sub>2 a))"

fun assigned_vars :: "assignment \<Rightarrow> vname set" where
  "assigned_vars [] = {}" |
  "assigned_vars ((v, _)#as) = {v} \<union> assigned_vars as"

definition "complete_assignment a e = (\<forall>v \<in> vars e. v \<in> assigned_vars a)"

definition "minimal_assignment a e = (\<forall>v \<in> assigned_vars a. v \<in> vars e)"

definition "complete_and_minimal_assignment a e \<longleftrightarrow> 
  (complete_assignment a e \<and> minimal_assignment a e)"
*)
(*
definition "unifiable e\<^sub>1 e\<^sub>2 = (\<exists>a. (assign e\<^sub>1 a) = (assign e\<^sub>2 a))"
*)

(* Substitution *)

fun substitute :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "substitute v (N n) _  = (N n)" |
  "substitute v (V v') e = (if v = v' then e else (V v'))" |
  "substitute v (Plus e\<^sub>1 e\<^sub>2) e = Plus (substitute v e\<^sub>1 e) (substitute v e\<^sub>2 e)"

lemma substitute_eq: "substitute v e (V v) = e"
  apply(induction e)
  apply(auto)
  done

lemma substitute_var_not_int_exp: "v \<notin> vars e \<Longrightarrow> substitute v e x = e"
  apply(induction e)
  apply(auto)
  done

lemma substitute_intermediate_var: 
  "y \<notin> vars e \<Longrightarrow> substitute y (substitute x e (V y)) e' = substitute x e e'"
  apply(induction e)
  apply(auto)
  done

lemma substitute_change_order: "x \<noteq> y \<Longrightarrow> x \<notin> vars u \<Longrightarrow> 
    substitute y (substitute x e t) u = substitute x (substitute y e u) (substitute y t u)"
  apply(induction e)
  apply(auto simp add:substitute_var_not_int_exp)
  done

lemma substitute_flip: "x \<noteq> y \<Longrightarrow> y \<notin> vars t \<Longrightarrow> x \<notin> vars u \<Longrightarrow>
  substitute y (substitute x e t) u = substitute x (substitute y e u) t"
  apply(induction e)
  apply(auto simp add:substitute_var_not_int_exp)
  done






lemma substitution_no_new_vars: "vars (substitute v e t) \<subseteq> vars e \<union> vars t"
  apply(induction e)
  apply(auto)
  done

lemma substitution_removes_var: "v \<notin> vars t \<Longrightarrow> v \<notin> vars (substitute v e t)"
  apply(induction e)
  apply(auto)
  done

lemma no_vars_e_eq_sub_e: "vars e = {} \<Longrightarrow> substitute v e a = e"
  apply(induction e)
  apply(auto)
  done

lemma subst_adds_subt: "v \<in> vars e \<Longrightarrow> t \<in> subterms (substitute v e t)"
  apply(induction e)
  apply(auto simp add:e_is_subterm_e)
  done

lemma subst_is_strict_subt: "e \<noteq> V v \<Longrightarrow> v \<in> vars e \<Longrightarrow> t \<in> strict_subterms (substitute v e t)"
proof-
  assume "e \<noteq> V v" "v \<in> vars e"
  then show ?thesis
  proof(cases e)
    case (N x1)
    then show ?thesis using \<open>v \<in> vars e\<close> by auto 
  next
    case (V x2)
    then show ?thesis using \<open>e \<noteq> V v\<close> \<open>v \<in> vars e\<close> by force 
  next
    case (Plus e1 e2)
    have "v \<in> vars e1 \<or> v \<in> vars e2" using Plus \<open>v \<in> vars e\<close> by auto
    have "\<exists>f1 f2. substitute v e t = Plus f1 f2" using Plus by force 
    from this obtain f1 f2 where 0: "substitute v e t = Plus f1 f2" by blast
    then show ?thesis
    proof(cases "v \<in> vars e1")
      case True
      have "t \<in> subterms f1" using 0 Plus True subst_adds_subt by auto 
      then show ?thesis by (simp add: 0 strict_subt_of_plus) 
    next
      case False
      have "v \<in> vars e2" using False \<open>v \<in> vars e1 \<or> v \<in> vars e2\<close> by force 
      hence "t \<in> subterms f2" using 0 Plus \<open>v \<in> vars e2\<close> subst_adds_subt by auto 
      then show ?thesis by (simp add: 0 strict_subt_of_plus) 
    qed
  qed
qed

lemma e_not_eq_subst: "e \<noteq> V v \<Longrightarrow> v \<in> vars e \<Longrightarrow> substitute v e t \<noteq> t"
proof(induction e)
  case (Plus e1 e2)
  have 0: "v \<in> vars e1 \<or> v \<in> vars e2" using Plus.prems(2) by auto 
  then show ?case 
  proof(cases "v \<in> vars e1")
    case True
    then show ?thesis
    proof(cases "e1 = V v")
      case False
      then show ?thesis
        by (metis Plus.prems(1) Plus.prems(2) e_does_not_contain_e subst_is_strict_subt) 
    qed simp
  next
    case False
    have "v \<in> vars e2" using 0 False by simp
    then show ?thesis
    proof(cases "e2 = V v")
      case False
      then show ?thesis
        by (metis Plus.prems(1) Plus.prems(2) e_does_not_contain_e subst_is_strict_subt) 
    qed simp
  qed
qed simp_all

lemma subst_pres_subt: "f \<in> subterms e \<Longrightarrow> substitute v f t \<in> subterms (substitute v e t)"
  apply(induction e)
  apply(auto simp add:e_is_subterm_e)
  done

(* Simultaneous Substitutions *)

type_synonym substitutions = "(vname * aexp) list"

fun substitute' :: "substitutions \<Rightarrow> aexp \<Rightarrow> aexp" where
  "substitute' [] e = e" |
  "substitute' ((v, e')#st) e = substitute' st (substitute v e e')"

lemma no_vars_e_eq_sub'_e: "vars e = {} \<Longrightarrow> substitute' s e = e"
  apply(induction s)
  apply(auto simp add:no_vars_e_eq_sub_e)
  done

(* todo *)
lemma not_eq_impl_subst_not_eq:
  "f \<in> subterms e \<Longrightarrow> e \<noteq> f \<Longrightarrow> substitute v e t \<noteq> substitute v f t"
proof(induction e)
  case (Plus e1 e2)
  have 0:"f \<in> subterms e1 \<or> f \<in> subterms e2" using Plus.prems(1) Plus.prems(2) by auto
  then show ?case
  proof(cases "f \<in> subterms e1")
    case True
    then show ?thesis
    proof(cases "e1 = f")
      case False
      have "substitute v e1 t \<noteq> substitute v f t"
        using False Plus.IH(1) True by linarith
      then show ?thesis
        by (metis True Un_iff e_does_not_contain_e strict_subt_of_plus subst_pres_subt substitute.simps(3)) 
    qed simp
  next
    case False
    have "f \<in> subterms e2" using False 0 by force 
    then show ?thesis
    proof(cases "e2 = f")
      case False
      have "substitute v e2 t \<noteq> substitute v f t"
        using False Plus.IH(2) \<open>f \<in> subterms e2\<close> by fastforce 
      then show ?thesis
        by (metis UnI2 \<open>f \<in> subterms e2\<close> e_is_subterm_e subst_pres_subt subt_not_parent subterms.simps(3)) 
    qed simp
  qed
qed simp_all

lemma not_eq_impl_subst'_not_eq: 
  "f \<in> subterms e \<Longrightarrow> e \<noteq> f \<Longrightarrow> substitute' s e \<noteq> substitute' s f"
proof(induction s arbitrary: e f)
  case (Cons sh st)
  have "\<exists>a e'. sh = (a, e')" by simp 
  from this obtain a e' where "sh = (a, e')" by blast
  have "substitute' (sh#st) e = substitute' st (substitute a e e')" using \<open>sh = (a, e')\<close> by auto 
  moreover
  have "substitute' (sh#st) f = substitute' st (substitute a f e')" using \<open>sh = (a, e')\<close> by auto 
  ultimately
  have "substitute a f e' \<noteq> substitute a e e'" 
    by (metis Cons.prems(1) Cons.prems(2) not_eq_impl_subst_not_eq)
  moreover
  have "substitute a f e' \<in> subterms (substitute a e e')"
    using Cons.prems(1) subst_pres_subt by presburger 
  ultimately
  show ?case using Cons.IH \<open>sh = (a, e')\<close> substitute'.simps(2) by presburger 
qed simp

lemma plus_subst_to_plus: "\<exists>f\<^sub>1 f\<^sub>2. substitute' s (Plus e\<^sub>1 e\<^sub>2) = Plus f\<^sub>1 f\<^sub>2"
proof(induction s arbitrary: e\<^sub>1 e\<^sub>2)
  case Nil
  then show ?case by simp 
next
  case (Cons sh st)
  have "\<exists>a e'. sh = (a, e')" by simp 
  from this obtain a e' where "sh = (a, e')" by blast
  hence "substitute' (Cons sh st) (Plus e\<^sub>1 e\<^sub>2) = 
    substitute' st (Plus (substitute a e\<^sub>1 e') (substitute a e\<^sub>2 e'))" by simp
  moreover
  have "\<exists>f\<^sub>1 f\<^sub>2. substitute' st (Plus (substitute a e\<^sub>1 e') (substitute a e\<^sub>2 e')) =
    Plus f\<^sub>1 f\<^sub>2" using local.Cons by force 
  ultimately 
  show ?case by presburger 
qed

(* Unifier *)

definition "unifiable e\<^sub>1 e\<^sub>2 \<longleftrightarrow>  (\<exists>s. substitute' s e\<^sub>1 = substitute' s e\<^sub>2)"
definition "unifier s e\<^sub>1 e\<^sub>2 \<longleftrightarrow> (substitute' s e\<^sub>1 = substitute' s e\<^sub>2)"

lemma unifier_eq_unifiable: "unifiable e\<^sub>1 e\<^sub>2 \<longleftrightarrow> (\<exists>s. unifier s e\<^sub>1 e\<^sub>2)"
proof
  assume "unifiable e\<^sub>1 e\<^sub>2"
  then show "\<exists>s. unifier s e\<^sub>1 e\<^sub>2" 
    using unifiable_def unifier_def by auto 
next
  assume "\<exists>s. unifier s e\<^sub>1 e\<^sub>2"
  then show "unifiable e\<^sub>1 e\<^sub>2"
    using unifiable_def unifier_def by auto 
qed

lemma unifier_com: "unifier s e\<^sub>1 e\<^sub>2 \<longleftrightarrow> unifier s e\<^sub>2 e\<^sub>1"
  using unifier_def by fastforce 

lemma v_in_e_not_unif: "v \<in> vars e \<Longrightarrow> V v \<noteq> e \<Longrightarrow> \<not>unifiable (V v) e" 
proof
  assume assm0: "v \<in> vars e" 
  assume assm1: "V v \<noteq> e"
  assume assm2: "unifiable (V v) e"
  hence "\<exists>s. unifier s (V v) e" using unifier_eq_unifiable by auto 
  from this obtain s where s_unif: "unifier s (V v) e" by blast
  have "v \<in> vars e \<Longrightarrow> V v \<noteq> e \<Longrightarrow> unifier s (V v) e \<Longrightarrow> False"
  proof(induction s arbitrary: e)
    case Nil
    then show ?case by (simp add: unifier_def) 
  next
    case (Cons sh st)
    have "\<exists>a e'. sh = (a, e')" by simp
    from this obtain a e' where " sh = (a, e')" by blast
    have "(substitute' (Cons sh st) e = substitute' (Cons sh st) (V v))"
      using Cons.prems(3) unifier_def by fastforce 
    hence 0: "substitute' st (substitute a e e') = substitute' st (substitute a (V v) e')"
      by (simp add: \<open>sh = (a, e')\<close>)
    then show ?case
    proof(cases "a = v")
      case True
      have "substitute a (V v) e' = e'" by (simp add: True)
      moreover
      have "e' \<in> subterms (substitute a e e')" using assm0
        using Cons.prems(1) True subst_adds_subt by presburger
      moreover
      have "substitute a e e' \<noteq> e'"
        using Cons.prems(1) Cons.prems(2) True e_not_eq_subst by auto 
      ultimately
      show ?thesis using 0 not_eq_impl_subst'_not_eq by auto 
    next
      case False
      have 1:"substitute a (V v) e' = (V v)" by (simp add: False)
      hence "substitute' st (substitute a e e') = substitute' st (V v)" using 0 by presburger 
      moreover 
      have "(V v) \<in> subterms (substitute a e e')"
        by (metis Cons.prems(1) 1 subst_adds_subt subst_pres_subt substitute_eq)
      moreover
      have "substitute' st (substitute a e e') \<noteq> substitute' st (V v)"
        by (metis "1" Cons.prems(1) Cons.prems(2) calculation(2) not_eq_impl_subst'_not_eq not_eq_impl_subst_not_eq psubsetD strict_subt_le_subt subst_is_strict_subt substitute_eq) 
      ultimately
      have "False" by blast 
      then show ?thesis.
    qed
  qed
  thus False using assm0 assm1 s_unif by fastforce 
qed

fun have_common_root :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "have_common_root (N _) (N _) = True" |
  "have_common_root (V _) (V _) = True" |
  "have_common_root (Plus _ _) (Plus _ _) = True" |
  "have_common_root _ _ = False"

fun is_var :: "aexp \<Rightarrow> bool" where
  "is_var (V _) = True" |
  "is_var _ = False"

lemma no_common_root_no_var_impl_non_unif:
  "\<not>have_common_root e\<^sub>1 e\<^sub>2 \<Longrightarrow> \<not>is_var e\<^sub>1 \<Longrightarrow> \<not>is_var e\<^sub>2 \<Longrightarrow> \<not>unifiable e\<^sub>1 e\<^sub>2"
proof(induction e\<^sub>1 e\<^sub>2 rule:have_common_root.induct)
  case ("4_3" f\<^sub>1 f\<^sub>2 n)
  have "\<not>unifiable (Plus f\<^sub>1 f\<^sub>2) (N n)"
  proof(rule ccontr)
    assume "\<not>\<not>unifiable (Plus f\<^sub>1 f\<^sub>2) (N n)"
    hence "unifiable (Plus f\<^sub>1 f\<^sub>2) (N n)" by blast
    hence "\<exists>s. unifier s (Plus f\<^sub>1 f\<^sub>2) (N n)" using unifier_eq_unifiable by auto 
    from this obtain s where "unifier s (Plus f\<^sub>1 f\<^sub>2) (N n)" by blast
    hence 0: "substitute' s (Plus f\<^sub>1 f\<^sub>2) = substitute' s (N n)" using unifier_def by blast 
    hence "\<exists>f\<^sub>1' f\<^sub>2'. substitute' s (Plus f\<^sub>1 f\<^sub>2) = Plus f\<^sub>1' f\<^sub>2'" using plus_subst_to_plus by blast
    from this obtain f\<^sub>1' f\<^sub>2' where "substitute' s (Plus f\<^sub>1 f\<^sub>2) = Plus f\<^sub>1' f\<^sub>2'" by blast
    moreover
    have "substitute' s (N n) = N n" by (simp add: no_vars_e_eq_sub'_e) 
    moreover
    have "substitute' s (Plus f\<^sub>1 f\<^sub>2) \<noteq> substitute' s (N n)"
      by (simp add: calculation(1) calculation(2)) 
    then show False using 0 by blast
  qed
  then show ?case by simp 
next
  case ("4_7" n e\<^sub>1 e\<^sub>2)
  have "unifiable (N n) (Plus e\<^sub>1 e\<^sub>2) = unifiable (Plus e\<^sub>1 e\<^sub>2) (N n)"
    by (simp add: unifier_com unifier_eq_unifiable)
  moreover
  have "\<not>unifiable (Plus e\<^sub>1 e\<^sub>2) (N n)" 
    by (metis aexp.distinct(3) no_vars_e_eq_sub'_e plus_subst_to_plus unifiable_def vars.simps(1)) 
  then show ?case by (simp add: calculation) 
qed simp_all

lemma subst_plus_subst_child:
  "substitute' s (Plus e\<^sub>1 e\<^sub>2) = Plus (substitute' s e\<^sub>1) (substitute' s e\<^sub>2)"
  apply(induction s arbitrary: e\<^sub>1 e\<^sub>2)
  apply(auto)
  done

(* Finding a neccessary improvement for the substitution *)

definition "num_vars e = card (vars e)"

lemma vars_subst_e_sub_vars_e: "vars t \<subseteq> vars e \<Longrightarrow> vars (substitute v e t) \<subseteq> vars e"
  using substitution_no_new_vars by blast

lemma vars_subst_e_strict_sub_vars_e: 
  "vars t \<subseteq> vars e \<Longrightarrow> v \<in> vars e \<Longrightarrow> v \<notin> vars t \<Longrightarrow> vars (substitute v e t) \<subset> vars e"
  by (metis vars_subst_e_sub_vars_e psubsetI substitution_removes_var)

(*
fun distance :: "aexp \<Rightarrow> aexp \<Rightarrow> nat" where
  "distance (N n\<^sub>1) (N n\<^sub>2) = (if n\<^sub>1 = n\<^sub>2 then 0 else 1)" |
  "distance (V v\<^sub>1) (V v\<^sub>2) = (if v\<^sub>1 = v\<^sub>2 then 0 else 1)" |
  "distance (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) = max (distance e\<^sub>1 f\<^sub>1) (distance e\<^sub>2 f\<^sub>2)" |
  "distance _ _ = 1"
*)
(* distance e\<^sub>1 f\<^sub>1 + distance e\<^sub>2 f\<^sub>2" | *)

(*
lemma dist_0_eq_id: "e\<^sub>1 = e\<^sub>2 \<longleftrightarrow> distance e\<^sub>1 e\<^sub>2 = 0"
  apply(induction e\<^sub>1 e\<^sub>2 rule:distance.induct)
  apply(auto)
  done

lemma unifier_dist_0: "unifier s e\<^sub>1 e\<^sub>2 \<longleftrightarrow> distance (substitute' s e\<^sub>1) (substitute' s e\<^sub>2) = 0"
  by (simp add: dist_0_eq_id unifier_def)
*)

(*
fun is_in :: "vname \<Rightarrow> aexp \<Rightarrow> bool" where
  "is_in v (N _) = False" |
  "is_in v (V v') = (v = v')" |
  "is_in v (Plus e\<^sub>1 e\<^sub>2) = (is_in v e\<^sub>1 \<or> is_in v e\<^sub>2)"

lemma is_in_eq_is_elem: "is_in v e \<longleftrightarrow> v \<in> vars e"
  apply(induction e)
  apply(auto)
  done
*)

datatype substitution = None | NonSubst | Subst vname aexp

fun find_substitution :: "aexp \<Rightarrow> aexp \<Rightarrow> substitution" where
  "find_substitution (N n\<^sub>1) (N n\<^sub>2) = (if n\<^sub>1 = n\<^sub>2 then None else NonSubst)" |
  "find_substitution (N n) (V v) = Subst v (N n)" |
  "find_substitution (N _) (Plus _ _) = NonSubst" |
  "find_substitution (V v) (N n) = Subst v (N n)" |
  "find_substitution (V v\<^sub>1) (V v\<^sub>2) = (if v\<^sub>1 = v\<^sub>2 then None else Subst v\<^sub>1 (V v\<^sub>2))" |
  "find_substitution (V v) (Plus e\<^sub>1 e\<^sub>2) = (if v \<in> vars (Plus e\<^sub>1 e\<^sub>2) then NonSubst else Subst v (Plus e\<^sub>1 e\<^sub>2))" |
  "find_substitution (Plus _ _) (N _) = NonSubst" |
  "find_substitution (Plus e\<^sub>1 e\<^sub>2) (V v) = (if v \<in> vars (Plus e\<^sub>1 e\<^sub>2) then NonSubst else Subst v (Plus e\<^sub>1 e\<^sub>2))" |
  "find_substitution (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) = (case find_substitution e\<^sub>1 f\<^sub>1 of
      None \<Rightarrow> find_substitution e\<^sub>2 f\<^sub>2 |
      NonSubst \<Rightarrow> NonSubst |
      Subst v e \<Rightarrow> Subst v e
  )"

lemma find_subst_var_in_e: "find_substitution e\<^sub>1 e\<^sub>2 = Subst v e \<Longrightarrow> v \<in> vars e\<^sub>1 \<or> v \<in> vars e\<^sub>2"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:if_splits substitution.splits)
  done

lemma find_subst_e_in_es: "find_substitution e\<^sub>1 e\<^sub>2 = Subst v e \<Longrightarrow> e \<in> subterms e\<^sub>1 \<or> e \<in> subterms e\<^sub>2"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:if_splits substitution.splits)
  done

lemma find_subst_plus_in_child: 
  "find_substitution (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) = Subst v e \<Longrightarrow> 
  find_substitution e\<^sub>1 f\<^sub>1 = Subst v e \<or> find_substitution e\<^sub>2 f\<^sub>2 = Subst v e"
  by (metis find_substitution.simps(9) substitution.exhaust substitution.simps(10) substitution.simps(8) substitution.simps(9))

lemma no_subst_es_eq:"find_substitution e\<^sub>1 e\<^sub>2 = None \<longleftrightarrow> e\<^sub>1 = e\<^sub>2" 
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma subst_found_es_eq: "find_substitution e\<^sub>1 e\<^sub>2 = Subst v e' \<Longrightarrow> e\<^sub>1 \<noteq> e\<^sub>2"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma non_subst_es_not_eq: "find_substitution e\<^sub>1 e\<^sub>2 = NonSubst \<Longrightarrow> e\<^sub>1 \<noteq> e\<^sub>2"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

(*
lemma no_subst_eq_dist_0: "find_substitution e\<^sub>1 e\<^sub>2 = None \<longleftrightarrow> distance e\<^sub>1 e\<^sub>2 = 0"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma subst_found_eq_pos_dist: "find_substitution e\<^sub>1 e\<^sub>2 = Subst v e \<Longrightarrow> distance e\<^sub>1 e\<^sub>2 > 0"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma non_subst_eq_pos_dist: "find_substitution e\<^sub>1 e\<^sub>2 = NonSubst \<Longrightarrow> distance e\<^sub>1 e\<^sub>2 > 0"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

corollary pos_dist_eq_subst_or_non_subst: 
  "((\<exists>v e. find_substitution e\<^sub>1 e\<^sub>2 = Subst v e) \<or> 
  (find_substitution e\<^sub>1 e\<^sub>2 = NonSubst)) \<longleftrightarrow> distance e\<^sub>1 e\<^sub>2 > 0"
  by (metis bot_nat_0.not_eq_extremum no_subst_eq_dist_0 non_subst_eq_pos_dist substitution.distinct(3) substitution.exhaust) 
*)

(*
lemma "find_substitution e\<^sub>1 e\<^sub>2 = NonSubst \<Longrightarrow> 
  find_substitution (substitute v e\<^sub>1 t) (substitute v e\<^sub>2 t) = NonSubst"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply(auto split:if_splits)
  sorry
*)

(*
lemma find_subst_eq_none_eq_id: "find_substitution e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
  by (simp add: dist_0_eq_id no_subst_eq_dist_0) 
*)

(*
lemma unif_plus_unif_child:
  "unifiable (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) \<Longrightarrow> unifiable e\<^sub>1 f\<^sub>1 \<and> unifiable e\<^sub>2 f\<^sub>2"
  using subst_plus_subst_child unifiable_def by auto
*)

(*
lemma unif_plus_unif_right:
  "unifiable (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) \<Longrightarrow> unifiable e\<^sub>2 f\<^sub>2" 
proof(rule ccontr)
  assume assm0: "unifiable (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2)"
  assume assm1: "\<not>unifiable e\<^sub>2 f\<^sub>2"
  hence 0: "\<forall>s. substitute' s e\<^sub>2 \<noteq> substitute' s f\<^sub>2" using unifiable_def by blast 
  have "\<exists>s. substitute' s (Plus e\<^sub>1 e\<^sub>2) = substitute' s (Plus f\<^sub>1 f\<^sub>2)" using assm0 unifiable_def by force 
  from this obtain s where 1:"substitute' s (Plus e\<^sub>1 e\<^sub>2) = substitute' s (Plus f\<^sub>1 f\<^sub>2)" by blast
  have "\<not>unifiable e\<^sub>2 f\<^sub>2 \<Longrightarrow> substitute' s (Plus e\<^sub>1 e\<^sub>2) = substitute' s (Plus f\<^sub>1 f\<^sub>2) \<Longrightarrow> False" for e\<^sub>1 e\<^sub>2 f\<^sub>1 f\<^sub>2
  proof(induction s)
    case Nil
    then show ?case
      by (simp add: unifiable_def) 
  next
    case (Cons sh st)
    show ?case
      using 0 1 subst_plus_subst_child by force
  qed
  then show False using 1 assm1 by blast 
qed
*)

lemma find_subst_none_impl_unif:
  "find_substitution e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> unifiable e\<^sub>1 e\<^sub>2"
  by (simp add: no_subst_es_eq unifiable_def)
(*
proof-
  assume "find_substitution e\<^sub>1 e\<^sub>2 = None"
  hence "e\<^sub>1 = e\<^sub>2" using dist_0_eq_id no_subst_eq_dist_0 by auto
  hence "substitute' [] e\<^sub>1 = substitute' [] e\<^sub>2" by simp
  hence "unifier [] e\<^sub>1 e\<^sub>2" using unifier_def by force 
  thus "unifiable e\<^sub>1 e\<^sub>2" using unifier_eq_unifiable by force 
qed
*)

lemma find_subst_non_subst_impl_not_unif:
  "find_substitution e\<^sub>1 e\<^sub>2 = NonSubst \<Longrightarrow> \<not>unifiable e\<^sub>1 e\<^sub>2"
proof(rule ccontr)
  assume assm0: "find_substitution e\<^sub>1 e\<^sub>2 = NonSubst"
  assume assm1: "\<not> \<not>unifiable e\<^sub>1 e\<^sub>2"
  hence "unifiable e\<^sub>1 e\<^sub>2" by blast
  hence "\<exists>s. unifier s e\<^sub>1 e\<^sub>2" using unifier_eq_unifiable by blast 
  from this obtain s where "unifier s e\<^sub>1 e\<^sub>2" by blast
  have "find_substitution e\<^sub>1 e\<^sub>2 = NonSubst \<Longrightarrow> unifier s e\<^sub>1 e\<^sub>2 \<Longrightarrow> False"
  proof(induction e\<^sub>1 e\<^sub>2 rule: find_substitution.induct)
    case (1 n\<^sub>1 n\<^sub>2)
    then show ?case by (simp add: no_vars_e_eq_sub'_e unifier_def) 
  next
    case (3 uu uv uw)
    then show ?case using no_common_root_no_var_impl_non_unif unifier_eq_unifiable by auto 
  next
    case (5 v\<^sub>1 v\<^sub>2)
    then show ?case by (metis find_substitution.simps(5) substitution.distinct(1) substitution.distinct(5)) 
  next
    case (6 v e\<^sub>1 e\<^sub>2)
    then show ?case
      by (metis aexp.simps(9) find_substitution.simps(6) substitution.distinct(6) unifier_eq_unifiable v_in_e_not_unif) 
  next
    case (7 ux uy uz)
    then show ?case
      using no_common_root_no_var_impl_non_unif unifier_eq_unifiable by auto 
  next
    case (8 e\<^sub>1 e\<^sub>2 v)
    then show ?case
      by (metis aexp.distinct(5) find_substitution.simps(8) substitution.distinct(5) unifiable_def unifier_def v_in_e_not_unif) 
  next
    case (9 e\<^sub>1 e\<^sub>2 f\<^sub>1 f\<^sub>2)
    then show ?case 
    proof(induction "find_substitution e\<^sub>1 f\<^sub>1" rule:substitution.induct)
      case None
      then show ?case using None.hyps None.prems(2) None.prems(4) subst_plus_subst_child unifier_def by auto 
    next
      case NonSubst
      then show ?case by (simp add: subst_plus_subst_child unifier_def) 
    next
      case (Subst x1 x2)
      then show ?case by (metis find_substitution.simps(9) substitution.distinct(5) substitution.simps(10)) 
    qed
  qed simp_all
  then show False using \<open>unifier s e\<^sub>1 e\<^sub>2\<close> assm0 by blast 
qed

(* ============================= *)

(*
lemma find_subst_reduces_dist: "find_substitution e\<^sub>1 e\<^sub>2 = Subst v e \<Longrightarrow>
  distance e\<^sub>1 e\<^sub>2 > 0 \<Longrightarrow> unifiable e\<^sub>1 e\<^sub>2 \<Longrightarrow> 
  distance (substitute v e\<^sub>1 e) (substitute v e\<^sub>2 e) < distance e\<^sub>1 e\<^sub>2"
proof(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  case (6 v e\<^sub>1 e\<^sub>2)
  have 0: "\<not>is_in v e\<^sub>1" "\<not>is_in v e\<^sub>2" using "6.prems"(1) by force+
  hence "e = Plus e\<^sub>1 e\<^sub>2" using "6.prems"(1) by auto 
  have "substitute v e\<^sub>1 e = e\<^sub>1" 
    using "0"(1) is_in_eq_is_elem substitute_var_not_int_exp by blast 
  have "substitute v e\<^sub>2 e = e\<^sub>2"
    using "0"(2) is_in_eq_is_elem substitute_var_not_int_exp by auto 
  then show ?case
    by (metis "6.prems"(1) \<open>substitute v e\<^sub>1 e = e\<^sub>1\<close> dist_0_eq_id distance.simps(11) find_substitution.simps(6) less_one substitute.simps(2) substitute.simps(3) substitution.distinct(5) substitution.inject) 
next
  case (8 e\<^sub>1 e\<^sub>2 v)
  then show ?case 
    by (metis dist_0_eq_id find_substitution.simps(8) is_in_eq_is_elem substitute.simps(2) substitute_var_not_int_exp substitution.distinct(5) substitution.inject) 
next
  case (9 e\<^sub>1 e\<^sub>2 f\<^sub>1 f\<^sub>2) 
  then show ?case
  proof(induction "find_substitution e\<^sub>1 f\<^sub>1" rule:substitution.induct)
    case None
    have 0:"find_substitution e\<^sub>2 f\<^sub>2 = Subst v e" using None.hyps None.prems(3) by auto 
    have "unifiable e\<^sub>2 f\<^sub>2" using None.prems(5) subst_plus_subst_child unifiable_def by auto 
    hence "distance (substitute v e\<^sub>2 e) (substitute v f\<^sub>2 e) < distance e\<^sub>2 f\<^sub>2"
      by (simp add: None.hyps None.prems(2) 0 subst_found_eq_pos_dist) 
    then show ?case
      by (metis None.hyps dist_0_eq_id distance.simps(3) max_nat.left_neutral no_subst_eq_dist_0 substitute.simps(3)) 
  next
    case (Subst v e')
    have "distance (substitute v e\<^sub>1 e) (substitute v f\<^sub>1 e) < distance e\<^sub>1 f\<^sub>1"
      by (smt (verit) Subst.hyps Subst.prems(1) Subst.prems(3) Subst.prems(5) aexp.inject(3) find_substitution.simps(9) subst_found_eq_pos_dist subst_plus_subst_child substitution.inject substitution.simps(10) unifiable_def) 
    then show ?case sorry
  qed simp
qed(auto split:if_splits)
*)

lemma find_subst_le_vars: "find_substitution e\<^sub>1 e\<^sub>2 = Subst v t \<Longrightarrow> 
  vars (substitute v e\<^sub>1 t) \<union> vars (substitute v e\<^sub>2 t) \<subset> vars e\<^sub>1 \<union> vars e\<^sub>2"
  apply(induction e\<^sub>1 e\<^sub>2 rule:find_substitution.induct)
  apply (metis find_substitution.simps(1) substitution.distinct(6) substitution.simps(5))
  using find_subst_var_in_e apply auto[1]
  apply simp
  using no_vars_e_eq_sub_e apply auto[1]
  apply force
  apply (metis Un_iff aexp.distinct(5) find_substitution.simps(6) order_less_le substitute.simps(2) substitute_var_not_int_exp substitution.distinct(5) substitution.inject sup.idem sup_ge2)
  apply simp
  apply (metis (mono_tags, lifting) Un_iff find_subst_var_in_e find_substitution.simps(8) order_less_le substitute.simps(2) substitute_var_not_int_exp substitution.distinct(5) substitution.inject sup.idem sup_ge1)
  sorry

lemma "find_substitution (substitute' s e\<^sub>1) (substitute' s e\<^sub>2) = Subst x31 x32 \<Longrightarrow>
       num_vars (substitute' (s @ [(x31, x32)]) e\<^sub>1) + num_vars (substitute' (s @ [(x31, x32)]) e\<^sub>2) < num_vars (substitute' s e\<^sub>1) + num_vars (substitute' s e\<^sub>2)"
  sorry

(* Unification of arithmetic expressions  *)

datatype aexpUnif = NonUnif | Unif substitutions

function unify' :: "substitutions \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexpUnif" where
  "unify' s e\<^sub>1 e\<^sub>2 = (case (substitute' s e\<^sub>1, substitute' s e\<^sub>2) of
    (s\<^sub>1, s\<^sub>2) \<Rightarrow> (if s\<^sub>1 = s\<^sub>2 then Unif s else 
      (case find_substitution s\<^sub>1 s\<^sub>2 of
        None \<Rightarrow> NonUnif |
        NonSubst \<Rightarrow> NonUnif |
        Subst v e \<Rightarrow> unify' (s@[(v, e)]) e\<^sub>1 e\<^sub>2
      )
    )
  )"
by pat_completeness auto
termination 
  apply(relation "measure (\<lambda>(s, e\<^sub>1, e\<^sub>2). num_vars (substitute' s e\<^sub>1) + num_vars (substitute' s e\<^sub>2))")
  apply(auto)
  sorry

definition "unify e\<^sub>1 e\<^sub>2 = unify' [] e\<^sub>1 e\<^sub>2"

value "unify (V x) (N 3)"
value "unify (Plus (V x) (N 3)) (Plus (N 3) (N 3))"
value "unify (Plus (N 4) (N 3)) (Plus (N 3) (N 3))"
value "unify (Plus (V ''x'') (N 3)) (Plus (V ''y'') (N 3))"
value "unify (Plus (N 3) (N 3)) (Plus (V x) (N 3))"
value "unify' [(''x'', N 3)] (N 3) (N 5)"
value "unify (Plus (N 3) (N 4)) (Plus (V ''x'') (N 4))"
value "unify (Plus (Plus (V ''y'') (N 3)) (N 4)) (Plus (V ''x'') (N 4))"

(*
lemma unify_dist_0: "unify e\<^sub>1 e\<^sub>2 = Unif (rev s) \<Longrightarrow> 
  distance (substitute' (rev s) e\<^sub>1) (substitute' (rev s) e\<^sub>2) = 0"
  apply(induction s)
  apply(auto simp add:unify_def split:substitution.splits)
  apply (meson aexpUnif.distinct(1))
      apply (meson aexpUnif.distinct(1))
  apply(simp split:if_splits) 
  sorry
*)

lemma unify'_es_eq: 
  "unify' s e\<^sub>1 e\<^sub>2 = Unif s' \<Longrightarrow> (substitute' s' e\<^sub>1) = (substitute' s' e\<^sub>2)"
  sorry

corollary unifiy'_unifies: "unify' s e\<^sub>1 e\<^sub>2 = Unif s' \<Longrightarrow> unifier s' e\<^sub>1 e\<^sub>2"
  using unifier_def unify'_es_eq by blast

lemma unifiable_impl_unif:"unifiable e\<^sub>1 e\<^sub>2 \<Longrightarrow> unify' [] e\<^sub>1 e\<^sub>2 = Unif s"
  sorry

lemma "unifiable e\<^sub>1 e\<^sub>2 \<longleftrightarrow> unify' [] e\<^sub>1 e\<^sub>2 = Unif s \<and> unifier s e\<^sub>1 e\<^sub>2"
  using unifiable_impl_unif unifier_eq_unifiable unifiy'_unifies by blast

theorem unifiable_correct1: "unifiable e\<^sub>1 e\<^sub>2 \<longleftrightarrow> unify e\<^sub>1 e\<^sub>2 = Unif s \<and> unifier s e\<^sub>1 e\<^sub>2"
  by (metis unifiable_impl_unif unifier_eq_unifiable unifiy'_unifies unify_def)

corollary unifiable_correct2: "unifiable e\<^sub>1 e\<^sub>2 \<longleftrightarrow> unify e\<^sub>1 e\<^sub>2 = NonUnif"
  by (metis aexpUnif.inject find_subst_none_impl_unif list.distinct(1) no_subst_es_eq unifiable_impl_unif)

(*
  apply(induction s' arbitrary: s e\<^sub>1 e\<^sub>2)
  apply(auto split:if_splits)
  using unifier_def apply presburger
  apply(auto split:substitution.splits)
  apply (simp add: no_subst_es_eq unifier_def)
  using non_subst_es_not_eq apply auto
  sorry
*)

(*
proof-
  let ?s\<^sub>1 = "substitute' s e\<^sub>1"
  let ?s\<^sub>2 = "substitute' s e\<^sub>2"
  show ?thesis
  proof(cases "distance ?s\<^sub>1 ?s\<^sub>2")
    case 0
    have "unify' s e\<^sub>1 e\<^sub>2 = Unif s" using "0" by force
    then show ?thesis sorry
  next
    case (Suc nat)
    then show ?thesis sorry
  qed
qed
*)

































(*

function unify' :: "substitution \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexpUnif" where
  "unify' s e\<^sub>1 e\<^sub>2 = (case (substitute' s e\<^sub>1, substitute' s e\<^sub>2) of
    (s\<^sub>1, s\<^sub>2) \<Rightarrow> (if distance s\<^sub>1 s\<^sub>2 = 0 then Unif s else 
      (case (s\<^sub>1, s\<^sub>2) of 
        (N _, N _) \<Rightarrow> NonUnif |
        (N n, V v) \<Rightarrow> unify' (s@[(v, N n)]) e\<^sub>1 e\<^sub>2 |
        (N _, Plus _ _) \<Rightarrow> NonUnif |
        (V v, N n) \<Rightarrow> unify' (s@[(v, N n)]) e\<^sub>1 e\<^sub>2 |
        (V v\<^sub>1, V v\<^sub>2) \<Rightarrow> unify' (s@[(v\<^sub>1, V v\<^sub>2)]) e\<^sub>1 e\<^sub>2 |
        (V v, Plus f\<^sub>1 f\<^sub>2) \<Rightarrow> unify' (s@[(v, Plus f\<^sub>1 f\<^sub>2)]) e\<^sub>1 e\<^sub>2 |
        (Plus _ _, N _) \<Rightarrow> NonUnif |
        (Plus f\<^sub>1 f\<^sub>2, V v) \<Rightarrow> unify' (s@[(v, Plus f\<^sub>1 f\<^sub>2)]) e\<^sub>1 e\<^sub>2 |
        (Plus f\<^sub>1 f\<^sub>2, Plus g\<^sub>1 g\<^sub>2) \<Rightarrow> (case unify' s f\<^sub>1 g\<^sub>1 of
          NonUnif \<Rightarrow> NonUnif |
          Unif s' \<Rightarrow> (if s' \<noteq> [] then unify' (s@s') e\<^sub>1 e\<^sub>2 else
          (case unify' s f\<^sub>2 g\<^sub>2 of 
            NonUnif \<Rightarrow> NonUnif |
            Unif s'' \<Rightarrow> unify' (s@s'') e\<^sub>1 e\<^sub>2
          ))
        )
      ))
  )"
by pat_completeness auto
termination 
  apply(relation "measure (\<lambda>(s, e\<^sub>1, e\<^sub>2). distance (substitute' s e\<^sub>1) (substitute' s e\<^sub>2))")
  apply(auto)
  sorry

definition "unify e\<^sub>1 e\<^sub>2 = unify' [] e\<^sub>1 e\<^sub>2"

value "unify (V x) (N 3)"
value "unify (Plus (V x) (N 3)) (Plus (N 3) (N 3))"
value "unify (V x) (N 3)"
value "unify (Plus (N 4) (N 3)) (Plus (N 3) (N 3))"
value "unify (Plus (V ''x'') (N 3)) (Plus (V ''y'') (N 3))"
value "unify (Plus (N 3) (N 3)) (Plus (V x) (N 3))"
value "unify' [(''x'', N 3)] (N 3) (N 5)"
value "unify (Plus (N 3) (N 4)) (Plus (V ''x'') (N 5))"
value "unify (Plus (Plus (V ''y'') (N 3)) (N 4)) (Plus (V ''x'') (N 5))"

*)


(*
function unify :: "aexp \<Rightarrow> aexp \<Rightarrow> aexpUnif" where
  "unify (N n\<^sub>1) (N n\<^sub>2) = (if n\<^sub>1 = n\<^sub>2 then Unif [] else NonUnif)" |
  "unify (N n) (V v) = Unif [(v, N n)]" |
  "unify (N _) (Plus _ _) = NonUnif" |
  "unify (V v) (N n) = Unif [(v, N n)]" |
  "unify (V v\<^sub>1) (V v\<^sub>2) = Unif [(v\<^sub>1, V v\<^sub>2)]" |
  "unify (V v) (Plus e\<^sub>1 e\<^sub>2) = Unif [(v, Plus e\<^sub>1 e\<^sub>2)]" |
  "unify (Plus _ _) (N _) = NonUnif" |
  "unify (Plus e\<^sub>1 e\<^sub>2) (V v) = Unif [(v, Plus e\<^sub>1 e\<^sub>2)]" |
  "unify (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) = (case unify e\<^sub>1 f\<^sub>1 of
      NonUnif \<Rightarrow> NonUnif |
      Unif s  \<Rightarrow> (case unify (substitute' s e\<^sub>2) (substitute' s f\<^sub>2) of
          NonUnif \<Rightarrow> NonUnif |
          Unif t  \<Rightarrow> Unif (s@t)
      )
  )"
by pat_completeness auto
termination apply(relation "measure (\<lambda>(e, f). num_vars e + num_vars f)")
  apply(auto)

value "unify (V ''x'') (Plus (N 3) (V ''y''))"
*)

(*
datatype aexpUnif = NonUnif | UnifL aexp aexp | UnifN aexpUnif aexpUnif

fun unify :: "aexp \<Rightarrow> aexp \<Rightarrow> aexpUnif" where
  "unify (N n\<^sub>1) (N n\<^sub>2) = (if n\<^sub>1 = n\<^sub>2 then UnifL (N n\<^sub>1) (N n\<^sub>2) else NonUnif)" |
  "unify (N n) (V v) = UnifL (N n) (V v)" |
  "unify (N _) (Plus _ _) = NonUnif" |
  "unify (V v) (N n) = UnifL (V v) (N n)" |
  "unify (V v\<^sub>1) (V v\<^sub>2) = UnifL (V v\<^sub>1) (V v\<^sub>2)" |
  "unify (V v) (Plus e\<^sub>1 e\<^sub>2) = UnifL (V v) (Plus e\<^sub>1 e\<^sub>2)" |
  "unify (Plus _ _) (N _) = NonUnif" |
  "unify (Plus e\<^sub>1 e\<^sub>2) (V v) = UnifL (Plus e\<^sub>1 e\<^sub>2) (V v)" |
  "unify (Plus e\<^sub>1 e\<^sub>2) (Plus f\<^sub>1 f\<^sub>2) = (case (unify e\<^sub>1 f\<^sub>1, unify e\<^sub>2 f\<^sub>2) of
      (NonUnif, _) \<Rightarrow> NonUnif |
      (_, NonUnif) \<Rightarrow> NonUnif |
      (u\<^sub>1, u\<^sub>2) \<Rightarrow> UnifN u\<^sub>1 u\<^sub>2
  )"

value "unify (N 5) (V ''x'')"
value "unify (Plus (N 4) (Plus (N 3) (N 2))) (Plus (N 4) (V ''y''))"
value "unify (Plus (N 4) (Plus (N 3) (N 2))) (Plus (N 3) (V ''y''))"
*)

(*
definition "unifiable e\<^sub>1 e\<^sub>2 = (unify e\<^sub>1 e\<^sub>2 \<noteq> NonUnif)"
*)

end
theory Submission
  imports Defs
begin

type_synonym vname = string

(* Arithmetic expressions *)

datatype aexp = N nat | V vname | Plus aexp aexp 

fun subterms :: "aexp ⇒ aexp set" where
  "subterms (N n) = {N n}" |
  "subterms (V v) = {V v}" |
  "subterms (Plus e⇩1 e⇩2) = {Plus e⇩1 e⇩2} ∪ subterms e⇩1 ∪ subterms e⇩2"

lemma e_is_subterm_e: "e ∈ subterms e" 
  apply(induction e)
  apply(auto)
  done

definition "strict_subterms e = subterms e - {e}"

lemma strict_subt_le_subt: "strict_subterms e ⊂ subterms e"
  using e_is_subterm_e order_less_le strict_subterms_def by auto 

lemma e_does_not_contain_e: "e ∉ strict_subterms e"
  by (simp add: strict_subterms_def)

lemma subt_trans: "f ∈ subterms e ⟹ g ∈ subterms f ⟹ g ∈ subterms e"
  apply(induction e)
  apply(auto)
  done

lemma subt_not_parent: "e ≠ f ⟹ f ∈ subterms e ⟹ e ∉ subterms f"
proof(induction e arbitrary: f)
  case (Plus e1 e2)
  have "f ∈ subterms e1 ∨ f ∈ subterms e2" using Plus.prems(1) Plus.prems(2) by auto 
  then show ?case
  proof(cases "f ∈ subterms e1")
    case True
    then show ?thesis
    proof(cases "f = e1")
      case True
      then show ?thesis using Plus.IH(1) Plus.prems(2) by force 
    next
      case False
      have "e1 ∉ subterms f" using False Plus.IH(1) True by presburger
      moreover
      have "e1 ∈ subterms (Plus e1 e2)" using e_is_subterm_e by auto
      moreover
      have "(Plus e1 e2) ∉ subterms f" using calculation(1) calculation(2) subt_trans by blast 
      ultimately
      show ?thesis by blast 
    qed
  next
    case False
    have "f ∈ subterms e2" using False ‹f ∈ subterms e1 ∨ f ∈ subterms e2› by auto 
    then show ?thesis
    proof(cases "f = e2")
      case True
      then show ?thesis using Plus.IH(2) Plus.prems(2) by force 
    next
      case False
      have "e2 ∉ subterms f" using False Plus.IH(2) ‹f ∈ subterms e2› by presburger 
      moreover
      have "e2 ∈ subterms (Plus e1 e2)" using e_is_subterm_e by fastforce 
      moreover
      have "(Plus e1 e2) ∉ subterms f" using calculation(1) calculation(2) subt_trans by blast 
      ultimately
      show ?thesis by blast 
    qed
  qed
qed simp_all

fun strict_subterms' :: "aexp ⇒ aexp set" where
  "strict_subterms' (N _) = {}" |
  "strict_subterms' (V _) = {}" |
  "strict_subterms' (Plus e⇩1 e⇩2) = subterms e⇩1 ∪ subterms e⇩2"

lemma strict_subt_eq_strict_subt': "strict_subterms e = strict_subterms' e"
proof(cases e)
  case (Plus e⇩1 e⇩2)
  have "strict_subterms e = subterms e - {e}" using strict_subterms_def by force 
  also have "… = ({Plus e⇩1 e⇩2} ∪ subterms e⇩1 ∪ subterms e⇩2) - {Plus e⇩1 e⇩2}"
    using Plus subterms.simps(3) by presburger 
  then show ?thesis
    using Plus Un_insert_left subt_not_parent calculation e_is_subterm_e by fastforce 
qed(simp_all add:strict_subterms_def)

corollary strict_subt_of_plus: "strict_subterms (Plus e⇩1 e⇩2) = subterms e⇩1 ∪ subterms e⇩2"
  by (simp add: strict_subt_eq_strict_subt')

fun vars :: "aexp ⇒ vname set" where
  "vars (N n) = {}" |
  "vars (V v) = {v}" |
  "vars (Plus e⇩1 e⇩2) = vars e⇩1 ∪ vars e⇩2"

(* Substitution *)

fun substitute :: "vname ⇒ aexp ⇒ aexp ⇒ aexp" where
  "substitute v (N n) _  = (N n)" |
  "substitute v (V v') e = (if v = v' then e else (V v'))" |
  "substitute v (Plus e⇩1 e⇩2) e = Plus (substitute v e⇩1 e) (substitute v e⇩2 e)"

lemma substitute_eq: "substitute v e (V v) = e"
  apply(induction e)
  apply(auto)
  done

lemma substitute_var_not_int_exp: "v ∉ vars e ⟹ substitute v e x = e"
  apply(induction e)
  apply(auto)
  done

lemma substitute_intermediate_var: 
  "y ∉ vars e ⟹ substitute y (substitute x e (V y)) e' = substitute x e e'"
  apply(induction e)
  apply(auto)
  done

lemma substitute_change_order: "x ≠ y ⟹ x ∉ vars u ⟹ 
    substitute y (substitute x e t) u = substitute x (substitute y e u) (substitute y t u)"
  apply(induction e)
  apply(auto simp add:substitute_var_not_int_exp)
  done

lemma substitute_flip: "x ≠ y ⟹ y ∉ vars t ⟹ x ∉ vars u ⟹
  substitute y (substitute x e t) u = substitute x (substitute y e u) t"
  apply(induction e)
  apply(auto simp add:substitute_var_not_int_exp)
  done

lemma substitution_no_new_vars: "vars (substitute v e t) ⊆ vars e ∪ vars t"
  apply(induction e)
  apply(auto)
  done

lemma substitution_removes_var: "v ∉ vars t ⟹ v ∉ vars (substitute v e t)"
  apply(induction e)
  apply(auto)
  done

lemma no_vars_e_eq_sub_e: "vars e = {} ⟹ substitute v e a = e"
  apply(induction e)
  apply(auto)
  done

lemma subst_adds_subt: "v ∈ vars e ⟹ t ∈ subterms (substitute v e t)"
  apply(induction e)
  apply(auto simp add:e_is_subterm_e)
  done

lemma subst_is_strict_subt: "e ≠ V v ⟹ v ∈ vars e ⟹ t ∈ strict_subterms (substitute v e t)"
proof-
  assume "e ≠ V v" "v ∈ vars e"
  then show ?thesis
  proof(cases e)
    case (N x1)
    then show ?thesis using ‹v ∈ vars e› by auto 
  next
    case (V x2)
    then show ?thesis using ‹e ≠ V v› ‹v ∈ vars e› by force 
  next
    case (Plus e1 e2)
    have "v ∈ vars e1 ∨ v ∈ vars e2" using Plus ‹v ∈ vars e› by auto
    have "∃f1 f2. substitute v e t = Plus f1 f2" using Plus by force 
    from this obtain f1 f2 where 0: "substitute v e t = Plus f1 f2" by blast
    then show ?thesis
    proof(cases "v ∈ vars e1")
      case True
      have "t ∈ subterms f1" using 0 Plus True subst_adds_subt by auto 
      then show ?thesis by (simp add: 0 strict_subt_of_plus) 
    next
      case False
      have "v ∈ vars e2" using False ‹v ∈ vars e1 ∨ v ∈ vars e2› by force 
      hence "t ∈ subterms f2" using 0 Plus ‹v ∈ vars e2› subst_adds_subt by auto 
      then show ?thesis by (simp add: 0 strict_subt_of_plus) 
    qed
  qed
qed

lemma e_not_eq_subst: "e ≠ V v ⟹ v ∈ vars e ⟹ substitute v e t ≠ t"
proof(induction e)
  case (Plus e1 e2)
  have 0: "v ∈ vars e1 ∨ v ∈ vars e2" using Plus.prems(2) by auto 
  then show ?case 
  proof(cases "v ∈ vars e1")
    case True
    then show ?thesis
    proof(cases "e1 = V v")
      case False
      then show ?thesis
        by (metis Plus.prems(1) Plus.prems(2) e_does_not_contain_e subst_is_strict_subt) 
    qed simp
  next
    case False
    have "v ∈ vars e2" using 0 False by simp
    then show ?thesis
    proof(cases "e2 = V v")
      case False
      then show ?thesis
        by (metis Plus.prems(1) Plus.prems(2) e_does_not_contain_e subst_is_strict_subt) 
    qed simp
  qed
qed simp_all

lemma subst_pres_subt: "f ∈ subterms e ⟹ substitute v f t ∈ subterms (substitute v e t)"
  apply(induction e)
  apply(auto simp add:e_is_subterm_e)
  done

lemma subst_other_vars_in_e: "x ≠ v ⟹ x ∈ vars e ⟹ x ∈ vars (substitute v e t)"
  apply(induction e)
  apply(auto)
  done

lemma vars_subst_e_sub_vars_e: "vars t ⊆ vars e ⟹ vars (substitute v e t) ⊆ vars e"
  using substitution_no_new_vars by blast

lemma vars_subst_e_strict_sub_vars_e: 
  "vars t ⊆ vars e ⟹ v ∈ vars e ⟹ v ∉ vars t ⟹ vars (substitute v e t) ⊂ vars e"
  by (metis vars_subst_e_sub_vars_e psubsetI substitution_removes_var)

(* Simultaneous Substitutions *)

type_synonym substitutions = "(vname * aexp) list"

fun substitute' :: "substitutions ⇒ aexp ⇒ aexp" where
  "substitute' [] e = e" |
  "substitute' ((v, e')#st) e = substitute' st (substitute v e e')"

lemma no_vars_e_eq_sub'_e: "vars e = {} ⟹ substitute' s e = e"
  apply(induction s)
  apply(auto simp add:no_vars_e_eq_sub_e)
  done

lemma not_eq_impl_subst_not_eq:
  "f ∈ subterms e ⟹ e ≠ f ⟹ substitute v e t ≠ substitute v f t"
proof(induction e)
  case (Plus e1 e2)
  have 0:"f ∈ subterms e1 ∨ f ∈ subterms e2" using Plus.prems(1) Plus.prems(2) by auto
  then show ?case
  proof(cases "f ∈ subterms e1")
    case True
    then show ?thesis
    proof(cases "e1 = f")
      case False
      have "substitute v e1 t ≠ substitute v f t"
        using False Plus.IH(1) True by linarith
      then show ?thesis
        by (metis True Un_iff e_does_not_contain_e strict_subt_of_plus subst_pres_subt substitute.simps(3)) 
    qed simp
  next
    case False
    have "f ∈ subterms e2" using False 0 by force 
    then show ?thesis
    proof(cases "e2 = f")
      case False
      have "substitute v e2 t ≠ substitute v f t"
        using False Plus.IH(2) ‹f ∈ subterms e2› by fastforce 
      then show ?thesis
        by (metis UnI2 ‹f ∈ subterms e2› e_is_subterm_e subst_pres_subt subt_not_parent subterms.simps(3)) 
    qed simp
  qed
qed simp_all

lemma not_eq_impl_subst'_not_eq: 
  "f ∈ subterms e ⟹ e ≠ f ⟹ substitute' s e ≠ substitute' s f"
proof(induction s arbitrary: e f)
  case (Cons sh st)
  have "∃a e'. sh = (a, e')" by simp 
  from this obtain a e' where "sh = (a, e')" by blast
  have "substitute' (sh#st) e = substitute' st (substitute a e e')" using ‹sh = (a, e')› by auto 
  moreover
  have "substitute' (sh#st) f = substitute' st (substitute a f e')" using ‹sh = (a, e')› by auto 
  ultimately
  have "substitute a f e' ≠ substitute a e e'" 
    by (metis Cons.prems(1) Cons.prems(2) not_eq_impl_subst_not_eq)
  moreover
  have "substitute a f e' ∈ subterms (substitute a e e')"
    using Cons.prems(1) subst_pres_subt by presburger 
  ultimately
  show ?case using Cons.IH ‹sh = (a, e')› substitute'.simps(2) by presburger 
qed simp

lemma plus_subst_to_plus: "∃f⇩1 f⇩2. substitute' s (Plus e⇩1 e⇩2) = Plus f⇩1 f⇩2"
proof(induction s arbitrary: e⇩1 e⇩2)
  case Nil
  then show ?case by simp 
next
  case (Cons sh st)
  have "∃a e'. sh = (a, e')" by simp 
  from this obtain a e' where "sh = (a, e')" by blast
  hence "substitute' (Cons sh st) (Plus e⇩1 e⇩2) = 
    substitute' st (Plus (substitute a e⇩1 e') (substitute a e⇩2 e'))" by simp
  moreover
  have "∃f⇩1 f⇩2. substitute' st (Plus (substitute a e⇩1 e') (substitute a e⇩2 e')) =
    Plus f⇩1 f⇩2" using local.Cons by force 
  ultimately 
  show ?case by presburger 
qed

(* Unifier *)

definition "unifiable e⇩1 e⇩2 ⟷  (∃s. substitute' s e⇩1 = substitute' s e⇩2)"
definition "unifier s e⇩1 e⇩2 ⟷ (substitute' s e⇩1 = substitute' s e⇩2)"

lemma unifier_eq_unifiable: "unifiable e⇩1 e⇩2 ⟷ (∃s. unifier s e⇩1 e⇩2)"
proof
  assume "unifiable e⇩1 e⇩2"
  then show "∃s. unifier s e⇩1 e⇩2" 
    using unifiable_def unifier_def by auto 
next
  assume "∃s. unifier s e⇩1 e⇩2"
  then show "unifiable e⇩1 e⇩2"
    using unifiable_def unifier_def by auto 
qed

lemma unifier_com: "unifier s e⇩1 e⇩2 ⟷ unifier s e⇩2 e⇩1"
  using unifier_def by fastforce 

lemma v_in_e_not_unif: "v ∈ vars e ⟹ V v ≠ e ⟹ ¬unifiable (V v) e" 
proof
  assume assm0: "v ∈ vars e" 
  assume assm1: "V v ≠ e"
  assume assm2: "unifiable (V v) e"
  hence "∃s. unifier s (V v) e" using unifier_eq_unifiable by auto 
  from this obtain s where s_unif: "unifier s (V v) e" by blast
  have "v ∈ vars e ⟹ V v ≠ e ⟹ unifier s (V v) e ⟹ False"
  proof(induction s arbitrary: e)
    case Nil
    then show ?case by (simp add: unifier_def) 
  next
    case (Cons sh st)
    have "∃a e'. sh = (a, e')" by simp
    from this obtain a e' where " sh = (a, e')" by blast
    have "(substitute' (Cons sh st) e = substitute' (Cons sh st) (V v))"
      using Cons.prems(3) unifier_def by fastforce 
    hence 0: "substitute' st (substitute a e e') = substitute' st (substitute a (V v) e')"
      by (simp add: ‹sh = (a, e')›)
    then show ?case
    proof(cases "a = v")
      case True
      have "substitute a (V v) e' = e'" by (simp add: True)
      moreover
      have "e' ∈ subterms (substitute a e e')" using assm0
        using Cons.prems(1) True subst_adds_subt by presburger
      moreover
      have "substitute a e e' ≠ e'"
        using Cons.prems(1) Cons.prems(2) True e_not_eq_subst by auto 
      ultimately
      show ?thesis using 0 not_eq_impl_subst'_not_eq by auto 
    next
      case False
      have 1:"substitute a (V v) e' = (V v)" by (simp add: False)
      hence "substitute' st (substitute a e e') = substitute' st (V v)" using 0 by presburger 
      moreover 
      have "(V v) ∈ subterms (substitute a e e')"
        by (metis Cons.prems(1) 1 subst_adds_subt subst_pres_subt substitute_eq)
      moreover
      have "substitute' st (substitute a e e') ≠ substitute' st (V v)"
        by (metis "1" Cons.prems(1) Cons.prems(2) calculation(2) not_eq_impl_subst'_not_eq not_eq_impl_subst_not_eq psubsetD strict_subt_le_subt subst_is_strict_subt substitute_eq) 
      ultimately
      have "False" by blast 
      then show ?thesis.
    qed
  qed
  thus False using assm0 assm1 s_unif by fastforce 
qed

fun have_common_root :: "aexp ⇒ aexp ⇒ bool" where
  "have_common_root (N _) (N _) = True" |
  "have_common_root (V _) (V _) = True" |
  "have_common_root (Plus _ _) (Plus _ _) = True" |
  "have_common_root _ _ = False"

fun is_var :: "aexp ⇒ bool" where
  "is_var (V _) = True" |
  "is_var _ = False"

lemma no_common_root_no_var_impl_non_unif:
  "¬have_common_root e⇩1 e⇩2 ⟹ ¬is_var e⇩1 ⟹ ¬is_var e⇩2 ⟹ ¬unifiable e⇩1 e⇩2"
proof(induction e⇩1 e⇩2 rule:have_common_root.induct)
  case ("4_3" f⇩1 f⇩2 n)
  have "¬unifiable (Plus f⇩1 f⇩2) (N n)"
  proof(rule ccontr)
    assume "¬¬unifiable (Plus f⇩1 f⇩2) (N n)"
    hence "unifiable (Plus f⇩1 f⇩2) (N n)" by blast
    hence "∃s. unifier s (Plus f⇩1 f⇩2) (N n)" using unifier_eq_unifiable by auto 
    from this obtain s where "unifier s (Plus f⇩1 f⇩2) (N n)" by blast
    hence 0: "substitute' s (Plus f⇩1 f⇩2) = substitute' s (N n)" using unifier_def by blast 
    hence "∃f⇩1' f⇩2'. substitute' s (Plus f⇩1 f⇩2) = Plus f⇩1' f⇩2'" using plus_subst_to_plus by blast
    from this obtain f⇩1' f⇩2' where "substitute' s (Plus f⇩1 f⇩2) = Plus f⇩1' f⇩2'" by blast
    moreover
    have "substitute' s (N n) = N n" by (simp add: no_vars_e_eq_sub'_e) 
    moreover
    have "substitute' s (Plus f⇩1 f⇩2) ≠ substitute' s (N n)"
      by (simp add: calculation(1) calculation(2)) 
    then show False using 0 by blast
  qed
  then show ?case by simp 
next
  case ("4_7" n e⇩1 e⇩2)
  have "unifiable (N n) (Plus e⇩1 e⇩2) = unifiable (Plus e⇩1 e⇩2) (N n)"
    by (simp add: unifier_com unifier_eq_unifiable)
  moreover
  have "¬unifiable (Plus e⇩1 e⇩2) (N n)" 
    by (metis aexp.distinct(3) no_vars_e_eq_sub'_e plus_subst_to_plus unifiable_def vars.simps(1)) 
  then show ?case by (simp add: calculation) 
qed simp_all

lemma subst_plus_subst_child:
  "substitute' s (Plus e⇩1 e⇩2) = Plus (substitute' s e⇩1) (substitute' s e⇩2)"
  apply(induction s arbitrary: e⇩1 e⇩2)
  apply(auto)
  done

(* Finding a neccessary improvement for the substitution *)

definition "num_vars e = card (vars e)"

datatype substitution = None | NonSubst | Subst vname aexp

fun find_substitution :: "aexp ⇒ aexp ⇒ substitution" where
  "find_substitution (N n⇩1) (N n⇩2) = (if n⇩1 = n⇩2 then None else NonSubst)" |
  "find_substitution (N n) (V v) = Subst v (N n)" |
  "find_substitution (N _) (Plus _ _) = NonSubst" |
  "find_substitution (V v) (N n) = Subst v (N n)" |
  "find_substitution (V v⇩1) (V v⇩2) = (if v⇩1 = v⇩2 then None else Subst v⇩1 (V v⇩2))" |
  "find_substitution (V v) (Plus e⇩1 e⇩2) = (if v ∈ vars (Plus e⇩1 e⇩2) then NonSubst else Subst v (Plus e⇩1 e⇩2))" |
  "find_substitution (Plus _ _) (N _) = NonSubst" |
  "find_substitution (Plus e⇩1 e⇩2) (V v) = (if v ∈ vars (Plus e⇩1 e⇩2) then NonSubst else Subst v (Plus e⇩1 e⇩2))" |
  "find_substitution (Plus e⇩1 e⇩2) (Plus f⇩1 f⇩2) = (case find_substitution e⇩1 f⇩1 of
      None ⇒ find_substitution e⇩2 f⇩2 |
      NonSubst ⇒ NonSubst |
      Subst v e ⇒ Subst v e
  )"

lemma find_subst_plus_in_child: 
  "find_substitution (Plus e⇩1 e⇩2) (Plus f⇩1 f⇩2) = Subst v e ⟹ 
  find_substitution e⇩1 f⇩1 = Subst v e ∨ find_substitution e⇩2 f⇩2 = Subst v e"
  by (metis find_substitution.simps(9) substitution.exhaust substitution.simps(10) substitution.simps(8) substitution.simps(9))

lemma no_subst_es_eq:"find_substitution e⇩1 e⇩2 = None ⟷ e⇩1 = e⇩2" 
  apply(induction e⇩1 e⇩2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma subst_found_es_eq: "find_substitution e⇩1 e⇩2 = Subst v e' ⟹ e⇩1 ≠ e⇩2"
  apply(induction e⇩1 e⇩2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma non_subst_es_not_eq: "find_substitution e⇩1 e⇩2 = NonSubst ⟹ e⇩1 ≠ e⇩2"
  apply(induction e⇩1 e⇩2 rule:find_substitution.induct)
  apply(auto split:substitution.splits)
  done

lemma find_subst_e_in_es: "find_substitution e⇩1 e⇩2 = Subst v e ⟹ vars e ⊆ vars e⇩1 ∪ vars e⇩2"
  apply(induction e⇩1 e⇩2 rule:find_substitution.induct)
  apply(auto split:if_splits substitution.splits)
  done

lemma find_subst_var_in_es: "find_substitution e⇩1 e⇩2 = Subst v e ⟹ v ∈ vars e⇩1 ∪ vars e⇩2"
  apply(induction e⇩1 e⇩2 rule:find_substitution.induct)
  apply(auto split:if_splits substitution.splits)
  done

lemma find_subst_v_not_in_e: "find_substitution e⇩1 e⇩2 = Subst v e ⟹ v ∉ vars e"
  apply(induction e⇩1 e⇩2 rule:find_substitution.induct)
  apply(auto split:if_splits substitution.splits)
  done

lemma find_subst_none_impl_unif:
  "find_substitution e⇩1 e⇩2 = None ⟹ unifiable e⇩1 e⇩2"
  by (simp add: no_subst_es_eq unifiable_def)

lemma find_subst_non_subst_impl_not_unif:
  "find_substitution e⇩1 e⇩2 = NonSubst ⟹ ¬unifiable e⇩1 e⇩2"
proof(rule ccontr)
  assume assm0: "find_substitution e⇩1 e⇩2 = NonSubst"
  assume assm1: "¬ ¬unifiable e⇩1 e⇩2"
  hence "unifiable e⇩1 e⇩2" by blast
  hence "∃s. unifier s e⇩1 e⇩2" using unifier_eq_unifiable by blast 
  from this obtain s where "unifier s e⇩1 e⇩2" by blast
  have "find_substitution e⇩1 e⇩2 = NonSubst ⟹ unifier s e⇩1 e⇩2 ⟹ False"
  proof(induction e⇩1 e⇩2 rule: find_substitution.induct)
    case (1 n⇩1 n⇩2)
    then show ?case by (simp add: no_vars_e_eq_sub'_e unifier_def) 
  next
    case (3 uu uv uw)
    then show ?case using no_common_root_no_var_impl_non_unif unifier_eq_unifiable by auto 
  next
    case (5 v⇩1 v⇩2)
    then show ?case by (metis find_substitution.simps(5) substitution.distinct(1) substitution.distinct(5)) 
  next
    case (6 v e⇩1 e⇩2)
    then show ?case
      by (metis aexp.simps(9) find_substitution.simps(6) substitution.distinct(6) unifier_eq_unifiable v_in_e_not_unif) 
  next
    case (7 ux uy uz)
    then show ?case
      using no_common_root_no_var_impl_non_unif unifier_eq_unifiable by auto 
  next
    case (8 e⇩1 e⇩2 v)
    then show ?case
      by (metis aexp.distinct(5) find_substitution.simps(8) substitution.distinct(5) unifiable_def unifier_def v_in_e_not_unif) 
  next
    case (9 e⇩1 e⇩2 f⇩1 f⇩2)
    then show ?case 
    proof(induction "find_substitution e⇩1 f⇩1" rule:substitution.induct)
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
  then show False using ‹unifier s e⇩1 e⇩2› assm0 by blast 
qed

lemma find_subst_impl_unif_impl_unif_e: 
  "find_substitution e⇩1 e⇩2 = Subst v t ⟹ unifiable (substitute v e⇩1 e) (substitute v e⇩2 e) ⟹ unifiable e⇩1 e⇩2"
  by (metis substitute'.simps(2) unifiable_def)

corollary find_subst_not_unif_impl_subst_not_unif:
  "find_substitution e⇩1 e⇩2 = Subst v e ⟹ ¬unifiable e⇩1 e⇩2 ⟹ ¬unifiable (substitute v e⇩1 e) (substitute v e⇩2 e)"
  using find_subst_impl_unif_impl_unif_e by blast

lemma find_subst_le_vars: "find_substitution e⇩1 e⇩2 = Subst v t ⟹ 
  vars (substitute v e⇩1 t) ∪ vars (substitute v e⇩2 t) ⊂ vars e⇩1 ∪ vars e⇩2"
  by (metis find_subst_e_in_es find_subst_v_not_in_e find_subst_var_in_es substitute.simps(3) vars.simps(3) vars_subst_e_strict_sub_vars_e)

lemma finite_vars: "finite (vars e)"
  apply(induction e)
  apply(auto)
  done

lemma card_vars_union_decr:
  "find_substitution e⇩1 e⇩2 = Subst v t ⟹ 
  card (vars (substitute v e⇩1 t) ∪ vars (substitute v e⇩2 t)) < card (vars e⇩1 ∪ vars e⇩2)"
proof-
  assume assm:"find_substitution e⇩1 e⇩2 = Subst v t"
  let ?s⇩1 = "vars (substitute v e⇩1 t) ∪ vars (substitute v e⇩2 t)"
  let ?s⇩2 = "vars e⇩1 ∪ vars e⇩2"
  have "finite ?s⇩2" by (simp add: finite_vars)
  moreover
  have "?s⇩1 ⊂ ?s⇩2" using assm find_subst_le_vars by presburger 
  ultimately 
  show ?thesis using psubset_card_mono[of ?s⇩2 ?s⇩1] by blast 
qed

lemma subst_subst':"substitute' (s@[(a, e')]) e = substitute a (substitute' s e) e'"
  apply(induction s e rule: substitute'.induct)
  apply(auto)
  done

(* Unification of arithmetic expressions  *)

datatype aexpUnif = NonUnif | Unif substitutions

function unify' :: "substitutions ⇒ aexp ⇒ aexp ⇒ aexpUnif" where
  "unify' s e⇩1 e⇩2 = (case (substitute' s e⇩1, substitute' s e⇩2) of
    (s⇩1, s⇩2) ⇒ (if s⇩1 = s⇩2 then Unif s else 
      (case find_substitution s⇩1 s⇩2 of
        None ⇒ NonUnif |
        NonSubst ⇒ NonUnif |
        Subst v e ⇒ unify' (s@[(v, e)]) e⇩1 e⇩2
      )
    )
  )"
by pat_completeness auto
termination 
  apply(relation "measure (λ(s, e⇩1, e⇩2). card (vars (substitute' s e⇩1) ∪ vars (substitute' s e⇩2)))")
  by(auto simp add:card_vars_union_decr subst_subst')

definition "unify e⇩1 e⇩2 = unify' [] e⇩1 e⇩2"

value "unify (V x) (N 3)"
value "unify (Plus (V x) (N 3)) (Plus (N 3) (N 3))"
value "unify (Plus (N 4) (N 3)) (Plus (N 3) (N 3))"
value "unify (Plus (V ''x'') (N 3)) (Plus (V ''y'') (N 3))"
value "unify (Plus (N 3) (N 3)) (Plus (V x) (N 3))"
value "unify' [(''x'', N 3)] (N 3) (N 5)"
value "unify (Plus (N 3) (N 4)) (Plus (V ''x'') (N 4))"
value "unify (Plus (Plus (V ''y'') (N 3)) (N 4)) (Plus (V ''x'') (N 4))"

lemma unify'_es_eq: 
  "unify' s e⇩1 e⇩2 = Unif s' ⟹ (substitute' s' e⇩1) = (substitute' s' e⇩2)" 
proof(induction s e⇩1 e⇩2 arbitrary: s' rule:unify'.induct)
  case (1 s e⇩1 e⇩2)
  let ?s⇩1 = "substitute' s e⇩1"
  let ?s⇩2 = "substitute' s e⇩2"
  from 1 show ?case 
  proof(cases "?s⇩1 = ?s⇩2")
    case True
    then show ?thesis using "1.prems" by fastforce 
  next
    case False
    have "∃v e. find_substitution ?s⇩1 ?s⇩2 = Subst v e"
      by (smt (verit) "1.prems" False aexpUnif.distinct(1) no_subst_es_eq old.prod.case substitution.exhaust substitution.simps(9) unify'.simps)
    from this obtain v e where 0:"find_substitution ?s⇩1 ?s⇩2 = Subst v e" by blast
    hence "unify' s e⇩1 e⇩2 = unify' (s@[(v, e)]) e⇩1 e⇩2" using False by auto 
    moreover
    have "unify' (s@[(v, e)]) e⇩1 e⇩2 = Unif s'"
      using "1.prems" calculation by presburger 
    ultimately
    show ?thesis using "1.IH" False 0 by blast 
  qed
qed

corollary unifiy'_unifies: "unify' s e⇩1 e⇩2 = Unif s' ⟹ unifier s' e⇩1 e⇩2"
  using unifier_def unify'_es_eq by blast

lemma aux:"unify' [] e⇩1 e⇩2 = NonUnif ⟹ ¬unifiable e⇩1 e⇩2" 
proof(rule ccontr)
  assume assm0:"unify' [] e⇩1 e⇩2 = NonUnif"
  assume assm1:"¬¬unifiable e⇩1 e⇩2"
  hence "unifiable e⇩1 e⇩2" by simp
  hence "∃s. unifier s e⇩1 e⇩2" using unifier_eq_unifiable by blast 
  then show False sorry
qed

lemma unifiable_impl_unif:"unifiable e⇩1 e⇩2 ⟹ (∃s. unify' [] e⇩1 e⇩2 = Unif s)"
proof(rule ccontr)
  assume assm0:"unifiable e⇩1 e⇩2"
  assume assm1:"∄s. unify' [] e⇩1 e⇩2 = Unif s"
  hence "∀s. unify' [] e⇩1 e⇩2 ≠ Unif s" by simp
  hence "unify' [] e⇩1 e⇩2 = NonUnif" by (meson aexpUnif.exhaust)
  then show False using assm0 aux by blast
qed

theorem unifiable_correct: "unifiable e⇩1 e⇩2 ⟷ (∃s. unify e⇩1 e⇩2 = Unif s ∧ unifier s e⇩1 e⇩2)"
  by (metis unifiable_impl_unif unifier_eq_unifiable unifiy'_unifies unify_def)

corollary unifiable_correct': "¬unifiable e⇩1 e⇩2 ⟷ unify e⇩1 e⇩2 = NonUnif"
  by (metis aexpUnif.exhaust aexpUnif.simps(3) unifiable_correct unifiy'_unifies unify_def) 









(*

function unify' :: "substitution ⇒ aexp ⇒ aexp ⇒ aexpUnif" where
  "unify' s e⇩1 e⇩2 = (case (substitute' s e⇩1, substitute' s e⇩2) of
    (s⇩1, s⇩2) ⇒ (if distance s⇩1 s⇩2 = 0 then Unif s else 
      (case (s⇩1, s⇩2) of 
        (N _, N _) ⇒ NonUnif |
        (N n, V v) ⇒ unify' (s@[(v, N n)]) e⇩1 e⇩2 |
        (N _, Plus _ _) ⇒ NonUnif |
        (V v, N n) ⇒ unify' (s@[(v, N n)]) e⇩1 e⇩2 |
        (V v⇩1, V v⇩2) ⇒ unify' (s@[(v⇩1, V v⇩2)]) e⇩1 e⇩2 |
        (V v, Plus f⇩1 f⇩2) ⇒ unify' (s@[(v, Plus f⇩1 f⇩2)]) e⇩1 e⇩2 |
        (Plus _ _, N _) ⇒ NonUnif |
        (Plus f⇩1 f⇩2, V v) ⇒ unify' (s@[(v, Plus f⇩1 f⇩2)]) e⇩1 e⇩2 |
        (Plus f⇩1 f⇩2, Plus g⇩1 g⇩2) ⇒ (case unify' s f⇩1 g⇩1 of
          NonUnif ⇒ NonUnif |
          Unif s' ⇒ (if s' ≠ [] then unify' (s@s') e⇩1 e⇩2 else
          (case unify' s f⇩2 g⇩2 of 
            NonUnif ⇒ NonUnif |
            Unif s'' ⇒ unify' (s@s'') e⇩1 e⇩2
          ))
        )
      ))
  )"
by pat_completeness auto
termination 
  apply(relation "measure (λ(s, e⇩1, e⇩2). distance (substitute' s e⇩1) (substitute' s e⇩2))")
  apply(auto)
  sorry

definition "unify e⇩1 e⇩2 = unify' [] e⇩1 e⇩2"

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
function unify :: "aexp ⇒ aexp ⇒ aexpUnif" where
  "unify (N n⇩1) (N n⇩2) = (if n⇩1 = n⇩2 then Unif [] else NonUnif)" |
  "unify (N n) (V v) = Unif [(v, N n)]" |
  "unify (N _) (Plus _ _) = NonUnif" |
  "unify (V v) (N n) = Unif [(v, N n)]" |
  "unify (V v⇩1) (V v⇩2) = Unif [(v⇩1, V v⇩2)]" |
  "unify (V v) (Plus e⇩1 e⇩2) = Unif [(v, Plus e⇩1 e⇩2)]" |
  "unify (Plus _ _) (N _) = NonUnif" |
  "unify (Plus e⇩1 e⇩2) (V v) = Unif [(v, Plus e⇩1 e⇩2)]" |
  "unify (Plus e⇩1 e⇩2) (Plus f⇩1 f⇩2) = (case unify e⇩1 f⇩1 of
      NonUnif ⇒ NonUnif |
      Unif s  ⇒ (case unify (substitute' s e⇩2) (substitute' s f⇩2) of
          NonUnif ⇒ NonUnif |
          Unif t  ⇒ Unif (s@t)
      )
  )"
by pat_completeness auto
termination apply(relation "measure (λ(e, f). num_vars e + num_vars f)")
  apply(auto)

value "unify (V ''x'') (Plus (N 3) (V ''y''))"
*)

(*
datatype aexpUnif = NonUnif | UnifL aexp aexp | UnifN aexpUnif aexpUnif

fun unify :: "aexp ⇒ aexp ⇒ aexpUnif" where
  "unify (N n⇩1) (N n⇩2) = (if n⇩1 = n⇩2 then UnifL (N n⇩1) (N n⇩2) else NonUnif)" |
  "unify (N n) (V v) = UnifL (N n) (V v)" |
  "unify (N _) (Plus _ _) = NonUnif" |
  "unify (V v) (N n) = UnifL (V v) (N n)" |
  "unify (V v⇩1) (V v⇩2) = UnifL (V v⇩1) (V v⇩2)" |
  "unify (V v) (Plus e⇩1 e⇩2) = UnifL (V v) (Plus e⇩1 e⇩2)" |
  "unify (Plus _ _) (N _) = NonUnif" |
  "unify (Plus e⇩1 e⇩2) (V v) = UnifL (Plus e⇩1 e⇩2) (V v)" |
  "unify (Plus e⇩1 e⇩2) (Plus f⇩1 f⇩2) = (case (unify e⇩1 f⇩1, unify e⇩2 f⇩2) of
      (NonUnif, _) ⇒ NonUnif |
      (_, NonUnif) ⇒ NonUnif |
      (u⇩1, u⇩2) ⇒ UnifN u⇩1 u⇩2
  )"

value "unify (N 5) (V ''x'')"
value "unify (Plus (N 4) (Plus (N 3) (N 2))) (Plus (N 4) (V ''y''))"
value "unify (Plus (N 4) (Plus (N 3) (N 2))) (Plus (N 3) (V ''y''))"
*)

(*
definition "unifiable e⇩1 e⇩2 = (unify e⇩1 e⇩2 ≠ NonUnif)"
*)

end

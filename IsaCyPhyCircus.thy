theory IsaCyPhyCircus
  imports "IsaCircus.IsaCircus" "Framed_ODEs.Framed_ODEs"
begin

unbundle Circus_Syntax

definition Dyn_SysC :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e) sfrd hrel" where
"Dyn_SysC x \<sigma> G = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [\<lambda> (s, s'). s' \<in> g_orbital_on x (\<lambda> t. \<sigma>) G (\<lambda> t. UNIV) UNIV 0 s]\<^sub>S)"

lemma rea_st_rel_unrest_ref [unrest]: "$ref\<^sup>< \<sharp> [R]\<^sub>S"
  unfolding rea_st_rel_def by (rule unrest_pred, expr_auto+)

lemma rea_st_rel_unrest_ref' [unrest]: "$ref\<^sup>> \<sharp> [R]\<^sub>S"
  unfolding rea_st_rel_def by (rule unrest_pred, expr_auto+)

lemma rea_st_rel_CRR [closure]: "[R]\<^sub>S is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)

lemma Dyn_SysC_NCSP [closure]: "Dyn_SysC x \<sigma> G is NCSP"
  unfolding Dyn_SysC_def by (rule closure, simp_all add: closure unrest)

lift_definition dyn_sys :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) action" 
  is "Dyn_SysC" by (simp add: closure)

syntax
  "_ode"             :: "derivs \<Rightarrow> logic \<Rightarrow> logic" ("{_ | _}")

translations
  "_ode \<sigma> G" => "CONST dyn_sys (_smaplets_svids \<sigma>) (_Subst \<sigma>) (G)\<^sub>e"

term "{x` = 1 | True} ;; a \<rightarrow> P"

end
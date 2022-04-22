theory ClosedForms imports
"BasicIdentities"
begin

lemma flts_middle0:
  shows "rflts (rsa @ RZERO # rsb) = rflts (rsa @ rsb)"
  apply(induct rsa)
  apply simp
  by (metis append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)



lemma simp_flatten_aux0:
  shows "rsimp (RALTS rs) = rsimp (RALTS (map rsimp rs))"
  by (metis append_Nil head_one_more_simp identity_wwo0 list.simps(8) rdistinct.simps(1) rflts.simps(1) rsimp.simps(2) rsimp_ALTs.simps(1) rsimp_ALTs.simps(3) simp_flatten spawn_simp_rsimpalts)
  

inductive 
  hrewrite:: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" ("_ h\<leadsto> _" [99, 99] 99)
where
  "RSEQ  RZERO r2 h\<leadsto> RZERO"
| "RSEQ  r1 RZERO h\<leadsto> RZERO"
| "RSEQ  RONE r h\<leadsto>  r"
| "r1 h\<leadsto> r2 \<Longrightarrow> RSEQ  r1 r3 h\<leadsto> RSEQ r2 r3"
| "r3 h\<leadsto> r4 \<Longrightarrow> RSEQ r1 r3 h\<leadsto> RSEQ r1 r4"
| "r h\<leadsto> r' \<Longrightarrow> (RALTS (rs1 @ [r] @ rs2)) h\<leadsto> (RALTS  (rs1 @ [r'] @ rs2))"
(*context rule for eliminating 0, alts--corresponds to the recursive call flts r::rs = r::(flts rs)*)
| "RALTS  (rsa @ [RZERO] @ rsb) h\<leadsto> RALTS  (rsa @ rsb)"
| "RALTS  (rsa @ [RALTS rs1] @ rsb) h\<leadsto> RALTS (rsa @ rs1 @ rsb)"
| "RALTS  [] h\<leadsto> RZERO"
| "RALTS  [r] h\<leadsto> r"
| "a1 = a2 \<Longrightarrow> RALTS (rsa@[a1]@rsb@[a2]@rsc) h\<leadsto> RALTS (rsa @ [a1] @ rsb @ rsc)"

inductive 
  hrewrites:: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" ("_ h\<leadsto>* _" [100, 100] 100)
where 
  rs1[intro, simp]:"r h\<leadsto>* r"
| rs2[intro]: "\<lbrakk>r1 h\<leadsto>* r2; r2 h\<leadsto> r3\<rbrakk> \<Longrightarrow> r1 h\<leadsto>* r3"


lemma hr_in_rstar : "r1 h\<leadsto> r2 \<Longrightarrow> r1 h\<leadsto>* r2"
  using hrewrites.intros(1) hrewrites.intros(2) by blast
 
lemma hreal_trans[trans]: 
  assumes a1: "r1 h\<leadsto>* r2"  and a2: "r2 h\<leadsto>* r3"
  shows "r1 h\<leadsto>* r3"
  using a2 a1
  apply(induct r2 r3 arbitrary: r1 rule: hrewrites.induct) 
  apply(auto)
  done

lemma hrewrites_seq_context:
  shows "r1 h\<leadsto>* r2 \<Longrightarrow> RSEQ r1 r3 h\<leadsto>* RSEQ r2 r3"
  apply(induct r1 r2 rule: hrewrites.induct)
   apply simp
  using hrewrite.intros(4) by blast

lemma hrewrites_seq_context2:
  shows "r1 h\<leadsto>* r2 \<Longrightarrow> RSEQ r0 r1 h\<leadsto>* RSEQ r0 r2"
  apply(induct r1 r2 rule: hrewrites.induct)
   apply simp
  using hrewrite.intros(5) by blast


lemma hrewrites_seq_contexts:
  shows "\<lbrakk>r1 h\<leadsto>* r2; r3 h\<leadsto>* r4\<rbrakk> \<Longrightarrow> RSEQ r1 r3 h\<leadsto>* RSEQ r2 r4"
  by (meson hreal_trans hrewrites_seq_context hrewrites_seq_context2)


lemma simp_removes_duplicate1:
  shows  " a \<in> set rsa \<Longrightarrow> rsimp (RALTS (rsa @ [a])) =  rsimp (RALTS (rsa))"
and " rsimp (RALTS (a1 # rsa @ [a1])) = rsimp (RALTS (a1 # rsa))"
  apply(induct rsa arbitrary: a1)
     apply simp
    apply simp
  prefer 2
  apply(case_tac "a = aa")
     apply simp
    apply simp
  apply (metis Cons_eq_appendI Cons_eq_map_conv distinct_removes_duplicate_flts list.set_intros(2))
  apply (metis append_Cons append_Nil distinct_removes_duplicate_flts list.set_intros(1) list.simps(8) list.simps(9))
  by (metis (mono_tags, lifting) append_Cons distinct_removes_duplicate_flts list.set_intros(1) list.simps(8) list.simps(9) map_append rsimp.simps(2))
  
lemma simp_removes_duplicate2:
  shows "a \<in> set rsa \<Longrightarrow> rsimp (RALTS (rsa @ [a] @ rsb)) = rsimp (RALTS (rsa @ rsb))"
  apply(induct rsb arbitrary: rsa)
   apply simp
  using distinct_removes_duplicate_flts apply auto[1]
  by (metis append.assoc head_one_more_simp rsimp.simps(2) simp_flatten simp_removes_duplicate1(1))

lemma simp_removes_duplicate3:
  shows "a \<in> set rsa \<Longrightarrow> rsimp (RALTS (rsa @ a # rsb)) = rsimp (RALTS (rsa @ rsb))"
  using simp_removes_duplicate2 by auto

(*
lemma distinct_removes_middle4:
  shows "a \<in> set rsa \<Longrightarrow> rdistinct (rsa @ [a] @ rsb) rset = rdistinct (rsa @ rsb) rset"
  using distinct_removes_middle(1) by fastforce
*)

(*
lemma distinct_removes_middle_list:
  shows "\<forall>a \<in> set x. a \<in> set rsa \<Longrightarrow> rdistinct (rsa @ x @ rsb) rset = rdistinct (rsa @ rsb) rset"
  apply(induct x)
   apply simp
  by (simp add: distinct_removes_middle3)
*)

inductive frewrite:: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> bool" ("_ \<leadsto>f _" [10, 10] 10)
  where
  "(RZERO # rs) \<leadsto>f rs"
| "((RALTS rs) # rsa) \<leadsto>f (rs @ rsa)"
| "rs1 \<leadsto>f rs2 \<Longrightarrow> (r # rs1) \<leadsto>f (r # rs2)"


inductive 
  frewrites:: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> bool" ("_ \<leadsto>f* _" [10, 10] 10)
where 
  [intro, simp]:"rs \<leadsto>f* rs"
| [intro]: "\<lbrakk>rs1 \<leadsto>f* rs2; rs2 \<leadsto>f rs3\<rbrakk> \<Longrightarrow> rs1 \<leadsto>f* rs3"

inductive grewrite:: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> bool" ("_ \<leadsto>g _" [10, 10] 10)
  where
  "(RZERO # rs) \<leadsto>g rs"
| "((RALTS rs) # rsa) \<leadsto>g (rs @ rsa)"
| "rs1 \<leadsto>g rs2 \<Longrightarrow> (r # rs1) \<leadsto>g (r # rs2)"
| "rsa @ [a] @ rsb @ [a] @ rsc \<leadsto>g rsa @ [a] @ rsb @ rsc" 

lemma grewrite_variant1:
  shows "a \<in> set rs1 \<Longrightarrow> rs1 @ a # rs \<leadsto>g rs1 @ rs"
  apply (metis append.assoc append_Cons append_Nil grewrite.intros(4) split_list_first)
  done


inductive 
  grewrites:: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> bool" ("_ \<leadsto>g* _" [10, 10] 10)
where 
  [intro, simp]:"rs \<leadsto>g* rs"
| [intro]: "\<lbrakk>rs1 \<leadsto>g* rs2; rs2 \<leadsto>g rs3\<rbrakk> \<Longrightarrow> rs1 \<leadsto>g* rs3"



(*
inductive 
  frewrites2:: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> bool" ("_ <\<leadsto>f* _" [10, 10] 10)
where 
 [intro]: "\<lbrakk>rs1 \<leadsto>f* rs2; rs2 \<leadsto>f* rs1\<rbrakk> \<Longrightarrow> rs1 <\<leadsto>f* rs2"
*)

lemma fr_in_rstar : "r1 \<leadsto>f r2 \<Longrightarrow> r1 \<leadsto>f* r2"
  using frewrites.intros(1) frewrites.intros(2) by blast
 
lemma freal_trans[trans]: 
  assumes a1: "r1 \<leadsto>f* r2"  and a2: "r2 \<leadsto>f* r3"
  shows "r1 \<leadsto>f* r3"
  using a2 a1
  apply(induct r2 r3 arbitrary: r1 rule: frewrites.induct) 
  apply(auto)
  done


lemma  many_steps_later: "\<lbrakk>r1 \<leadsto>f r2; r2 \<leadsto>f* r3 \<rbrakk> \<Longrightarrow> r1 \<leadsto>f* r3"
  by (meson fr_in_rstar freal_trans)


lemma gr_in_rstar : "r1 \<leadsto>g r2 \<Longrightarrow> r1 \<leadsto>g* r2"
  using grewrites.intros(1) grewrites.intros(2) by blast
 
lemma greal_trans[trans]: 
  assumes a1: "r1 \<leadsto>g* r2"  and a2: "r2 \<leadsto>g* r3"
  shows "r1 \<leadsto>g* r3"
  using a2 a1
  apply(induct r2 r3 arbitrary: r1 rule: grewrites.induct) 
  apply(auto)
  done


lemma  gmany_steps_later: "\<lbrakk>r1 \<leadsto>g r2; r2 \<leadsto>g* r3 \<rbrakk> \<Longrightarrow> r1 \<leadsto>g* r3"
  by (meson gr_in_rstar greal_trans)

lemma gstar_rdistinct_general:
  shows "rs1 @  rs \<leadsto>g* rs1 @ (rdistinct rs (set rs1))"
  apply(induct rs arbitrary: rs1)
   apply simp
  apply(case_tac " a \<in> set rs1")
   apply simp
  apply(subgoal_tac "rs1 @ a # rs \<leadsto>g rs1 @ rs")
  using gmany_steps_later apply auto[1]
  apply (metis append.assoc append_Cons append_Nil grewrite.intros(4) split_list_first)
  apply simp
  apply(drule_tac x = "rs1 @ [a]" in meta_spec)
  by simp


lemma gstar_rdistinct:
  shows "rs \<leadsto>g* rdistinct rs {}"
  apply(induct rs)
   apply simp
  by (metis append.left_neutral empty_set gstar_rdistinct_general)


lemma grewrite_append:
  shows "\<lbrakk> rsa \<leadsto>g rsb \<rbrakk> \<Longrightarrow> rs @ rsa \<leadsto>g rs @ rsb"
  apply(induct rs)
   apply simp+
  using grewrite.intros(3) by blast
  


lemma frewrites_cons:
  shows "\<lbrakk> rsa \<leadsto>f* rsb \<rbrakk> \<Longrightarrow> r # rsa \<leadsto>f* r # rsb"
  apply(induct rsa rsb rule: frewrites.induct)
   apply simp
  using frewrite.intros(3) by blast


lemma grewrites_cons:
  shows "\<lbrakk> rsa \<leadsto>g* rsb \<rbrakk> \<Longrightarrow> r # rsa \<leadsto>g* r # rsb"
  apply(induct rsa rsb rule: grewrites.induct)
   apply simp
  using grewrite.intros(3) by blast


lemma frewrites_append:
  shows " \<lbrakk>rsa \<leadsto>f* rsb\<rbrakk> \<Longrightarrow> (rs @ rsa) \<leadsto>f* (rs @ rsb)"
  apply(induct rs)
   apply simp
  by (simp add: frewrites_cons)

lemma grewrites_append:
  shows " \<lbrakk>rsa \<leadsto>g* rsb\<rbrakk> \<Longrightarrow> (rs @ rsa) \<leadsto>g* (rs @ rsb)"
  apply(induct rs)
   apply simp
  by (simp add: grewrites_cons)


lemma grewrites_concat:
  shows "\<lbrakk>rs1 \<leadsto>g rs2; rsa \<leadsto>g* rsb \<rbrakk> \<Longrightarrow> (rs1 @ rsa) \<leadsto>g* (rs2 @ rsb)"
  apply(induct rs1 rs2 rule: grewrite.induct)
    apply(simp)
  apply(subgoal_tac "(RZERO # rs @ rsa) \<leadsto>g (rs @ rsa)")
  prefer 2
  using grewrite.intros(1) apply blast
    apply(subgoal_tac "(rs @ rsa) \<leadsto>g* (rs @ rsb)")
  using gmany_steps_later apply blast
  apply (simp add: grewrites_append)
  apply (metis append.assoc append_Cons grewrite.intros(2) grewrites_append gmany_steps_later)
  using grewrites_cons apply auto
  apply(subgoal_tac "rsaa @ a # rsba @ a # rsc @ rsa \<leadsto>g* rsaa @ a # rsba @ a # rsc @ rsb")
  using grewrite.intros(4) grewrites.intros(2) apply force
  using grewrites_append by auto


lemma grewritess_concat:
  shows "\<lbrakk>rsa \<leadsto>g* rsb; rsc \<leadsto>g* rsd \<rbrakk> \<Longrightarrow> (rsa @ rsc) \<leadsto>g* (rsb @ rsd)"
  apply(induct rsa rsb rule: grewrites.induct)
   apply(case_tac rs)
    apply simp
  using grewrites_append apply blast   
  by (meson greal_trans grewrites.simps grewrites_concat)

fun alt_set:: "rrexp \<Rightarrow> rrexp set"
  where
  "alt_set (RALTS rs) = set rs \<union> \<Union> (alt_set ` (set rs))"
| "alt_set r = {r}"


lemma grewrite_cases_middle:
  shows "rs1 \<leadsto>g rs2 \<Longrightarrow> 
(\<exists>rsa rsb rsc. rs1 =  (rsa @ [RALTS rsb] @ rsc) \<and> rs2 = (rsa @ rsb @ rsc)) \<or>
(\<exists>rsa rsc. rs1 = rsa @ [RZERO] @ rsc \<and> rs2 = rsa @ rsc) \<or>
(\<exists>rsa rsb rsc a. rs1 = rsa @ [a] @ rsb @ [a] @ rsc \<and> rs2 = rsa @ [a] @ rsb @ rsc)"
  apply( induct rs1 rs2 rule: grewrite.induct)
     apply simp
  apply blast
  apply (metis append_Cons append_Nil)
  apply (metis append_Cons)
  by blast


lemma good_singleton:
  shows "good a \<and> nonalt a  \<Longrightarrow> rflts [a] = [a]"
  using good.simps(1) k0b by blast







lemma all_that_same_elem:
  shows "\<lbrakk> a \<in> rset; rdistinct rs {a} = []\<rbrakk>
       \<Longrightarrow> rdistinct (rs @ rsb) rset = rdistinct rsb rset"
  apply(induct rs)
   apply simp
  apply(subgoal_tac "aa = a")
   apply simp
  by (metis empty_iff insert_iff list.discI rdistinct.simps(2))

lemma distinct_early_app1:
  shows "rset1 \<subseteq> rset \<Longrightarrow> rdistinct rs rset = rdistinct (rdistinct rs rset1) rset"
  apply(induct rs arbitrary: rset rset1)
   apply simp
  apply simp
  apply(case_tac "a \<in> rset1")
   apply simp
   apply(case_tac "a \<in> rset")
    apply simp+
  
   apply blast
  apply(case_tac "a \<in> rset1")
   apply simp+
  apply(case_tac "a \<in> rset")
   apply simp
   apply (metis insert_subsetI)
  apply simp
  by (meson insert_mono)


lemma distinct_early_app:
  shows " rdistinct (rs @ rsb) rset = rdistinct (rdistinct rs {} @ rsb) rset"
  apply(induct rsb)
   apply simp
  using distinct_early_app1 apply blast
  by (metis distinct_early_app1 distinct_once_enough empty_subsetI)


lemma distinct_eq_interesting1:
  shows "a \<in> rset \<Longrightarrow> rdistinct (rs @ rsb) rset = rdistinct (rdistinct (a # rs) {} @ rsb) rset"
  apply(subgoal_tac "rdistinct (rdistinct (a # rs) {} @ rsb) rset = rdistinct (rdistinct rs {} @ rsb) rset")
   apply(simp only:)
  using distinct_early_app apply blast 
  by (metis append_Cons distinct_early_app rdistinct.simps(2))



lemma good_flatten_aux_aux1:
  shows "\<lbrakk> size rs \<ge>2; 
\<forall>r \<in> set rs. good r \<and> r \<noteq> RZERO \<and> nonalt r; \<forall>r \<in> set rsb. good r \<and> r \<noteq> RZERO \<and> nonalt r \<rbrakk>
       \<Longrightarrow> rdistinct (rs @ rsb) rset =
           rdistinct (rflts [rsimp_ALTs (rdistinct rs {})] @ rsb) rset"
  apply(induct rs arbitrary: rset)
   apply simp
  apply(case_tac "a \<in> rset")
   apply simp
   apply(case_tac "rdistinct rs {a}")
    apply simp
    apply(subst good_singleton)
     apply force
  apply simp
    apply (meson all_that_same_elem)
   apply(subgoal_tac "rflts [rsimp_ALTs (a # rdistinct rs {a})] = a # rdistinct rs {a} ")
  prefer 2
  using k0a rsimp_ALTs.simps(3) apply presburger
  apply(simp only:)
  apply(subgoal_tac "rdistinct (rs @ rsb) rset = rdistinct ((rdistinct (a # rs) {}) @ rsb) rset ")
    apply (metis insert_absorb insert_is_Un insert_not_empty rdistinct.simps(2))
   apply (meson distinct_eq_interesting1)
  apply simp
  apply(case_tac "rdistinct rs {a}")
  prefer 2
   apply(subgoal_tac "rsimp_ALTs (a # rdistinct rs {a}) = RALTS (a # rdistinct rs {a})")
  apply(simp only:)
  apply(subgoal_tac "a # rdistinct (rs @ rsb) (insert a rset) =
           rdistinct (rflts [RALTS (a # rdistinct rs {a})] @ rsb) rset")
   apply simp
  apply (metis append_Cons distinct_early_app empty_iff insert_is_Un k0a rdistinct.simps(2))
  using rsimp_ALTs.simps(3) apply presburger
  by (metis Un_insert_left append_Cons distinct_early_app empty_iff good_singleton rdistinct.simps(2) rsimp_ALTs.simps(2) sup_bot_left)



  

lemma good_flatten_aux_aux:
  shows "\<lbrakk>\<exists>a aa lista list. rs = a # list \<and> list = aa # lista; 
\<forall>r \<in> set rs. good r \<and> r \<noteq> RZERO \<and> nonalt r; \<forall>r \<in> set rsb. good r \<and> r \<noteq> RZERO \<and> nonalt r \<rbrakk>
       \<Longrightarrow> rdistinct (rs @ rsb) rset =
           rdistinct (rflts [rsimp_ALTs (rdistinct rs {})] @ rsb) rset"
  apply(erule exE)+
  apply(subgoal_tac "size rs \<ge> 2")
   apply (metis good_flatten_aux_aux1)
  by (simp add: Suc_leI length_Cons less_add_Suc1)



lemma good_flatten_aux:
  shows " \<lbrakk>\<forall>r\<in>set rs. good r \<or> r = RZERO; \<forall>r\<in>set rsa . good r \<or> r = RZERO; 
           \<forall>r\<in>set rsb. good r \<or> r = RZERO;
     rsimp (RALTS (rsa @ rs @ rsb)) = rsimp_ALTs (rdistinct (rflts (rsa @ rs @ rsb)) {});
     rsimp (RALTS (rsa @ [RALTS rs] @ rsb)) =
     rsimp_ALTs (rdistinct (rflts (rsa @ [rsimp (RALTS rs)] @ rsb)) {});
     map rsimp rsa = rsa; map rsimp rsb = rsb; map rsimp rs = rs;
     rdistinct (rflts rsa @ rflts rs @ rflts rsb) {} =
     rdistinct (rflts rsa) {} @ rdistinct (rflts rs @ rflts rsb) (set (rflts rsa));
     rdistinct (rflts rsa @ rflts [rsimp (RALTS rs)] @ rflts rsb) {} =
     rdistinct (rflts rsa) {} @ rdistinct (rflts [rsimp (RALTS rs)] @ rflts rsb) (set (rflts rsa))\<rbrakk>
    \<Longrightarrow>    rdistinct (rflts rs @ rflts rsb) rset =
           rdistinct (rflts [rsimp (RALTS rs)] @ rflts rsb) rset"
  apply simp
  apply(case_tac "rflts rs ")
   apply simp
  apply(case_tac "list")
   apply simp
   apply(case_tac "a \<in> rset")
    apply simp
  apply (metis append_Cons append_Nil flts_append list.set(1) list.simps(15) nonalt.simps(1) nonalt0_flts_keeps nonalt_flts_rd qqq1 rdistinct.simps(2) rdistinct_set_equality singleton_iff)
   apply simp
  apply (metis Un_insert_left append_Cons append_Nil ex_in_conv flts_single1 insertI1 list.simps(15) nonalt_flts_rd nonazero.elims(3) qqq1 rdistinct.simps(2) sup_bot_left)
  apply(subgoal_tac "\<forall>r \<in> set (rflts rs). good r \<and> r \<noteq> RZERO \<and> nonalt r")
  prefer 2  
  apply (metis flts3 nonalt_flts_rd qqq1 rdistinct_set_equality)
  apply(subgoal_tac "\<forall>r \<in> set (rflts rsb). good r \<and> r \<noteq> RZERO \<and> nonalt r")
  prefer 2  
  apply (metis flts3 nonalt_flts_rd qqq1 rdistinct_set_equality)
  by (smt (verit, ccfv_threshold) good_flatten_aux_aux)

  


lemma good_flatten_middle:
  shows "\<lbrakk>\<forall>r \<in> set rs. good r \<or> r = RZERO; \<forall>r \<in> set rsa. good r \<or> r = RZERO; \<forall>r \<in> set rsb. good r \<or> r = RZERO\<rbrakk> \<Longrightarrow>
rsimp (RALTS (rsa @ rs @ rsb)) = rsimp (RALTS (rsa @ [RALTS rs] @ rsb))"
  apply(subgoal_tac "rsimp (RALTS (rsa @ rs @ rsb)) = rsimp_ALTs (rdistinct (rflts (map rsimp rsa @ 
map rsimp rs @ map rsimp rsb)) {})")
  prefer 2
  apply simp
  apply(simp only:)
    apply(subgoal_tac "rsimp (RALTS (rsa @ [RALTS rs] @ rsb)) = rsimp_ALTs (rdistinct (rflts (map rsimp rsa @ 
[rsimp (RALTS rs)] @ map rsimp rsb)) {})")
  prefer 2
   apply simp
  apply(simp only:)
  apply(subgoal_tac "map rsimp rsa = rsa")
  prefer 2
  apply (metis map_idI rsimp.simps(3) test)
  apply(simp only:)
  apply(subgoal_tac "map rsimp rsb = rsb")
   prefer 2
  apply (metis map_idI rsimp.simps(3) test)
  apply(simp only:)
  apply(subst k00)+
  apply(subgoal_tac "map rsimp rs = rs")
   apply(simp only:)
   prefer 2
  apply (metis map_idI rsimp.simps(3) test)
  apply(subgoal_tac "rdistinct (rflts rsa @ rflts rs @ rflts rsb) {} = 
rdistinct (rflts rsa) {} @ rdistinct  (rflts rs @ rflts rsb) (set (rflts rsa))")
   apply(simp only:)
  prefer 2
  using rdistinct_concat_general apply blast
  apply(subgoal_tac "rdistinct (rflts rsa @ rflts [rsimp (RALTS rs)] @ rflts rsb) {} = 
rdistinct (rflts rsa) {} @ rdistinct  (rflts [rsimp (RALTS rs)] @ rflts rsb) (set (rflts rsa))")
   apply(simp only:)
  prefer 2
  using rdistinct_concat_general apply blast
  apply(subgoal_tac "rdistinct (rflts rs @ rflts rsb) (set (rflts rsa)) = 
                     rdistinct  (rflts [rsimp (RALTS rs)] @ rflts rsb) (set (rflts rsa))")
   apply presburger
  using good_flatten_aux by blast


lemma simp_flatten3:
  shows "rsimp (RALTS (rsa @ [RALTS rs] @ rsb)) = rsimp (RALTS (rsa @ rs @ rsb))"
  apply(subgoal_tac "rsimp (RALTS (rsa @ [RALTS rs] @ rsb)) = 
                     rsimp (RALTS (map rsimp rsa @ [rsimp (RALTS rs)] @ map rsimp rsb)) ")
  prefer 2
   apply (metis append.left_neutral append_Cons list.simps(9) map_append simp_flatten_aux0)
  apply (simp only:)
  apply(subgoal_tac "rsimp (RALTS (rsa @ rs @ rsb)) = 
rsimp (RALTS (map rsimp rsa @ map rsimp rs @ map rsimp rsb))")
  prefer 2
   apply (metis map_append simp_flatten_aux0)
  apply(simp only:)
  apply(subgoal_tac "rsimp  (RALTS (map rsimp rsa @ map rsimp rs @ map rsimp rsb)) =
 rsimp (RALTS (map rsimp rsa @ [RALTS (map rsimp rs)] @ map rsimp rsb))")
  
   apply (metis (no_types, lifting) head_one_more_simp map_append simp_flatten_aux0)
  apply(subgoal_tac "\<forall>r \<in> set (map rsimp rsa). good r \<or> r = RZERO")
   apply(subgoal_tac "\<forall>r \<in> set (map rsimp rs). good r \<or> r = RZERO")
    apply(subgoal_tac "\<forall>r \<in> set (map rsimp rsb). good r \<or> r = RZERO")
  
  using good_flatten_middle apply presburger
  
  apply (simp add: good1)
  apply (simp add: good1)
  apply (simp add: good1)

  done



  

lemma grewrite_equal_rsimp:
  shows "rs1 \<leadsto>g rs2 \<Longrightarrow> rsimp (RALTS rs1) = rsimp (RALTS rs2)"
  apply(frule grewrite_cases_middle)
  apply(case_tac "(\<exists>rsa rsb rsc. rs1 = rsa @ [RALTS rsb] @ rsc \<and> rs2 = rsa @ rsb @ rsc)")  
  using simp_flatten3 apply auto[1]
  apply(case_tac "(\<exists>rsa rsc. rs1 = rsa @ [RZERO] @ rsc \<and> rs2 = rsa @ rsc)")
  apply (metis (mono_tags, opaque_lifting) append_Cons append_Nil list.set_intros(1) list.simps(9) rflts.simps(2) rsimp.simps(2) rsimp.simps(3) simp_removes_duplicate3)
  by (smt (verit) append.assoc append_Cons append_Nil in_set_conv_decomp simp_removes_duplicate3)


lemma grewrites_equal_rsimp:
  shows "rs1 \<leadsto>g* rs2 \<Longrightarrow> rsimp (RALTS rs1) = rsimp (RALTS rs2)"
  apply (induct rs1 rs2 rule: grewrites.induct)
  apply simp
  using grewrite_equal_rsimp by presburger
  


lemma grewrites_last:
  shows "r # [RALTS rs] \<leadsto>g*  r # rs"
  by (metis gr_in_rstar grewrite.intros(2) grewrite.intros(3) self_append_conv)

lemma simp_flatten2:
  shows "rsimp (RALTS (r # [RALTS rs])) = rsimp (RALTS (r # rs))"
  using grewrites_equal_rsimp grewrites_last by blast


lemma frewrites_alt:
  shows "rs1 \<leadsto>f* rs2 \<Longrightarrow> (RALT r1 r2) # rs1 \<leadsto>f* r1 # r2 # rs2"  
  by (metis Cons_eq_appendI append_self_conv2 frewrite.intros(2) frewrites_cons many_steps_later)

lemma early_late_der_frewrites:
  shows "map (rder x) (rflts rs) \<leadsto>f* rflts (map (rder x) rs)"
  apply(induct rs)
   apply simp
  apply(case_tac a)
       apply simp+
  using frewrite.intros(1) many_steps_later apply blast
     apply(case_tac "x = x3")
      apply simp
  using frewrites_cons apply presburger
  using frewrite.intros(1) many_steps_later apply fastforce
  apply(case_tac "rnullable x41")
     apply simp+
     apply (simp add: frewrites_alt)
  apply (simp add: frewrites_cons)
   apply (simp add: frewrites_append)
  by (simp add: frewrites_cons)


lemma gstar0:
  shows "rsa @ (rdistinct rs (set rsa)) \<leadsto>g* rsa @ (rdistinct rs (insert RZERO (set rsa)))"
  apply(induct rs arbitrary: rsa)
   apply simp
  apply(case_tac "a = RZERO")
   apply simp
  
  using gr_in_rstar grewrite.intros(1) grewrites_append apply presburger
  apply(case_tac "a \<in> set rsa")
   apply simp+
  apply(drule_tac x = "rsa @ [a]" in meta_spec)
  by simp

lemma grewrite_rdistinct_aux:
  shows "rs @ rdistinct rsa rset \<leadsto>g* rs @ rdistinct rsa (rset \<union> set rs)"
  apply(induct rsa arbitrary: rs rset)
   apply simp
  apply(case_tac " a \<in> rset")
   apply simp
  apply(case_tac "a \<in> set rs")
  apply simp
   apply (metis Un_insert_left Un_insert_right gmany_steps_later grewrite_variant1 insert_absorb)
  apply simp
  apply(drule_tac x = "rs @ [a]" in meta_spec)
  by (metis Un_insert_left Un_insert_right append.assoc append.right_neutral append_Cons append_Nil insert_absorb2 list.simps(15) set_append)
  
 
lemma flts_gstar:
  shows "rs \<leadsto>g* rflts rs"
  apply(induct rs)
   apply simp
  apply(case_tac "a = RZERO")
   apply simp
  using gmany_steps_later grewrite.intros(1) apply blast
  apply(case_tac "\<exists>rsa. a = RALTS rsa")
   apply(erule exE)
  apply simp
   apply (meson grewrite.intros(2) grewrites.simps grewrites_cons)
  by (simp add: grewrites_cons rflts_def_idiot)

lemma more_distinct1:
  shows "       \<lbrakk>\<And>rsb rset rset2.
           rset2 \<subseteq> set rsb \<Longrightarrow> rsb @ rdistinct rs rset \<leadsto>g* rsb @ rdistinct rs (rset \<union> rset2);
        rset2 \<subseteq> set rsb; a \<notin> rset; a \<in> rset2\<rbrakk>
       \<Longrightarrow> rsb @ a # rdistinct rs (insert a rset) \<leadsto>g* rsb @ rdistinct rs (rset \<union> rset2)"
  apply(subgoal_tac "rsb @ a # rdistinct rs (insert a rset) \<leadsto>g* rsb @ rdistinct rs (insert a rset)")
   apply(subgoal_tac "rsb @ rdistinct rs (insert a rset) \<leadsto>g* rsb @ rdistinct rs (rset \<union> rset2)")
    apply (meson greal_trans)
   apply (metis Un_iff Un_insert_left insert_absorb)
  by (simp add: gr_in_rstar grewrite_variant1 in_mono)
  




lemma frewrite_rd_grewrites_aux:
  shows     "       RALTS rs \<notin> set rsb \<Longrightarrow>
       rsb @
       RALTS rs #
       rdistinct rsa
        (insert (RALTS rs)
          (set rsb)) \<leadsto>g* rflts rsb @
                          rdistinct rs (set rsb) @ rdistinct rsa (set rs \<union> set rsb \<union> {RALTS rs})"

   apply simp
  apply(subgoal_tac "rsb @
    RALTS rs #
    rdistinct rsa
     (insert (RALTS rs)
       (set rsb)) \<leadsto>g* rsb @
    rs @
    rdistinct rsa
     (insert (RALTS rs)
       (set rsb)) ")
  apply(subgoal_tac " rsb @
    rs @
    rdistinct rsa
     (insert (RALTS rs)
       (set rsb)) \<leadsto>g*
                      rsb @
    rdistinct rs (set rsb) @
    rdistinct rsa
     (insert (RALTS rs)
       (set rsb)) ")
    apply (smt (verit, ccfv_SIG) Un_insert_left flts_gstar greal_trans grewrite_rdistinct_aux grewritess_concat inf_sup_aci(5) rdistinct_concat_general rdistinct_set_equality set_append)
   apply (metis append_assoc grewrites.intros(1) grewritess_concat gstar_rdistinct_general)
  by (simp add: gr_in_rstar grewrite.intros(2) grewrites_append)
  



lemma list_dlist_union:
  shows "set rs \<subseteq> set rsb \<union> set (rdistinct rs (set rsb))"
  by (metis rdistinct_concat_general rdistinct_set_equality set_append sup_ge2)

lemma r_finite1:
  shows "r = RALTS (r # rs) = False"
  apply(induct r)
  apply simp+
   apply (metis list.set_intros(1))
  by blast
  


lemma grewrite_singleton:
  shows "[r] \<leadsto>g r # rs \<Longrightarrow> rs = []"
  apply (induct "[r]" "r # rs" rule: grewrite.induct)
    apply simp
  apply (metis r_finite1)
  using grewrite.simps apply blast
  by simp



lemma concat_rdistinct_equality1:
  shows "rdistinct (rs @ rsa) rset = rdistinct rs rset @ rdistinct rsa (rset \<union> (set rs))"
  apply(induct rs arbitrary: rsa rset)
   apply simp
  apply(case_tac "a \<in> rset")
   apply simp
  apply (simp add: insert_absorb)
  by auto


lemma grewrites_rev_append:
  shows "rs1 \<leadsto>g* rs2 \<Longrightarrow> rs1 @ [x] \<leadsto>g* rs2 @ [x]"
  using grewritess_concat by auto

lemma grewrites_inclusion:
  shows "set rs \<subseteq> set rs1 \<Longrightarrow> rs1 @ rs \<leadsto>g* rs1"
  apply(induct rs arbitrary: rs1)
  apply simp
  by (meson gmany_steps_later grewrite_variant1 list.set_intros(1) set_subset_Cons subset_code(1))

lemma distinct_keeps_last:
  shows "\<lbrakk>x \<notin> rset; x \<notin> set xs \<rbrakk> \<Longrightarrow> rdistinct (xs @ [x]) rset = rdistinct xs rset @ [x]"
  by (simp add: concat_rdistinct_equality1)

lemma grewrites_shape2_aux:
  shows "       RALTS rs \<notin> set rsb \<Longrightarrow>
       rsb @
       rdistinct (rs @ rsa)
        (set rsb) \<leadsto>g* rsb @
                       rdistinct rs (set rsb) @
                       rdistinct rsa (set rs \<union> set rsb \<union> {RALTS rs})"
  apply(subgoal_tac " rdistinct (rs @ rsa) (set rsb) =  rdistinct rs (set rsb) @ rdistinct rsa (set rs \<union> set rsb)")
   apply (simp only:)
  prefer 2
  apply (simp add: Un_commute concat_rdistinct_equality1)
  apply(induct rsa arbitrary: rs rsb rule: rev_induct)
   apply simp
  apply(case_tac "x \<in> set rs")
  apply (simp add: distinct_removes_middle3)
  apply(case_tac "x = RALTS rs")
   apply simp
  apply(case_tac "x \<in> set rsb")
   apply simp
    apply (simp add: concat_rdistinct_equality1)
  apply (simp add: concat_rdistinct_equality1)
  apply simp
  apply(drule_tac x = "rs " in meta_spec)
  apply(drule_tac x = rsb in meta_spec)
  apply simp
  apply(subgoal_tac " rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb) \<leadsto>g* rsb @ rdistinct rs (set rsb) @ rdistinct xs (insert (RALTS rs) (set rs \<union> set rsb))")
  prefer 2
   apply (simp add: concat_rdistinct_equality1)
  apply(case_tac "x \<in> set xs")
   apply simp
   apply (simp add: distinct_removes_last)
  apply(case_tac "x \<in> set rsb")
   apply (smt (verit, ccfv_threshold) Un_iff append.right_neutral concat_rdistinct_equality1 insert_is_Un rdistinct.simps(2))
  apply(subgoal_tac "rsb @ rdistinct rs (set rsb) @ rdistinct (xs @ [x]) (set rs \<union> set rsb) = rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb) @ [x]")
  apply(simp only:)
  apply(case_tac "x = RALTS rs")
    apply(subgoal_tac "rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb) @ [x] \<leadsto>g* rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb) @ rs")
  apply(subgoal_tac "rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb) @ rs \<leadsto>g* rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb) ")
      apply (smt (verit, ccfv_SIG) Un_insert_left append.right_neutral concat_rdistinct_equality1 greal_trans insert_iff rdistinct.simps(2))
  apply(subgoal_tac "set rs \<subseteq> set ( rsb @ rdistinct rs (set rsb) @ rdistinct xs (set rs \<union> set rsb))")
  apply (metis append.assoc grewrites_inclusion)
     apply (metis Un_upper1 append.assoc dual_order.trans list_dlist_union set_append)
  apply (metis append_Nil2 gr_in_rstar grewrite.intros(2) grewrite_append)
   apply(subgoal_tac " rsb @ rdistinct rs (set rsb) @ rdistinct (xs @ [x]) (insert (RALTS rs) (set rs \<union> set rsb)) =  rsb @ rdistinct rs (set rsb) @ rdistinct (xs) (insert (RALTS rs) (set rs \<union> set rsb)) @ [x]")
  apply(simp only:)
  apply (metis append.assoc grewrites_rev_append)
  apply (simp add: insert_absorb)
   apply (simp add: distinct_keeps_last)+
  done

lemma grewrites_shape2:
  shows "       RALTS rs \<notin> set rsb \<Longrightarrow>
       rsb @
       rdistinct (rs @ rsa)
        (set rsb) \<leadsto>g* rflts rsb @
                       rdistinct rs (set rsb) @
                       rdistinct rsa (set rs \<union> set rsb \<union> {RALTS rs})"
  apply (meson flts_gstar greal_trans grewrites.simps grewrites_shape2_aux grewritess_concat)
  done

lemma rdistinct_add_acc:
  shows "rset2 \<subseteq> set rsb \<Longrightarrow> rsb @ rdistinct rs rset \<leadsto>g* rsb @ rdistinct rs (rset \<union> rset2)"
  apply(induct rs arbitrary: rsb rset rset2)
   apply simp
  apply (case_tac "a \<in> rset")
   apply simp
  apply(case_tac "a \<in> rset2")
   apply simp
  apply (simp add: more_distinct1)
  apply simp
  apply(drule_tac x = "rsb @ [a]" in meta_spec)
  by (metis Un_insert_left append.assoc append_Cons append_Nil set_append sup.coboundedI1)
  

lemma frewrite_fun1:
  shows "       RALTS rs \<in> set rsb \<Longrightarrow>
       rsb @ rdistinct rsa (set rsb) \<leadsto>g* rflts rsb @ rdistinct rsa (set rsb \<union> set rs)"
  apply(subgoal_tac "rsb @ rdistinct rsa (set rsb) \<leadsto>g* rflts rsb @ rdistinct rsa (set rsb)")
   apply(subgoal_tac " set rs \<subseteq> set (rflts rsb)")
  prefer 2
  using spilled_alts_contained apply blast
   apply(subgoal_tac "rflts rsb @ rdistinct rsa (set rsb) \<leadsto>g* rflts rsb @ rdistinct rsa (set rsb \<union> set rs)")
  using greal_trans apply blast
  using rdistinct_add_acc apply presburger
  using flts_gstar grewritess_concat by auto
  
lemma frewrite_rd_grewrites:
  shows "rs1 \<leadsto>f rs2 \<Longrightarrow> 
\<exists>rs3. (rs @ (rdistinct rs1 (set rs)) \<leadsto>g* rs3) \<and> (rs @ (rdistinct rs2 (set rs)) \<leadsto>g* rs3) "
  apply(induct rs1 rs2 arbitrary: rs rule: frewrite.induct)
    apply(rule_tac x = "rsa @ (rdistinct rs ({RZERO} \<union> set rsa))" in exI)
    apply(rule conjI)
  apply(case_tac "RZERO \<in> set rsa")
  apply simp+
  using gstar0 apply fastforce
     apply (simp add: gr_in_rstar grewrite.intros(1) grewrites_append)
    apply (simp add: gstar0)
    prefer 2
    apply(case_tac "r \<in> set rs")
  apply simp
    apply(drule_tac x = "rs @ [r]" in meta_spec)
    apply(erule exE)
    apply(rule_tac x = "rs3" in exI)
   apply simp
  apply(case_tac "RALTS rs \<in> set rsb")
   apply simp
   apply(rule_tac x = "rflts rsb @ rdistinct rsa (set rsb \<union> set rs)" in exI)
   apply(rule conjI)
  using frewrite_fun1 apply force
  apply (metis frewrite_fun1 rdistinct_concat sup_ge2)
  apply(simp)
  apply(rule_tac x = 
 "rflts rsb @
                       rdistinct rs (set rsb) @
                       rdistinct rsa (set rs \<union> set rsb \<union> {RALTS rs})" in exI)
  apply(rule conjI)
   prefer 2
  using grewrites_shape2 apply force
  using frewrite_rd_grewrites_aux by blast


lemma frewrite_simpeq2:
  shows "rs1 \<leadsto>f rs2 \<Longrightarrow> rsimp (RALTS (rdistinct rs1 {})) = rsimp (RALTS (rdistinct rs2 {}))"
  apply(subgoal_tac "\<exists> rs3. (rdistinct rs1 {} \<leadsto>g* rs3) \<and> (rdistinct rs2 {} \<leadsto>g* rs3)")
  using grewrites_equal_rsimp apply fastforce
  by (metis append_self_conv2 frewrite_rd_grewrites list.set(1))




(*a more refined notion of h\<leadsto>* is needed,
this lemma fails when rs1 contains some RALTS rs where elements
of rs appear in later parts of rs1, which will be picked up by rs2
and deduplicated*)
lemma frewrites_simpeq:
  shows "rs1 \<leadsto>f* rs2 \<Longrightarrow>
 rsimp (RALTS (rdistinct rs1 {})) = rsimp (RALTS ( rdistinct rs2 {})) "
  apply(induct rs1 rs2 rule: frewrites.induct)
   apply simp
  using frewrite_simpeq2 by presburger


lemma frewrite_single_step:
  shows " rs2 \<leadsto>f rs3 \<Longrightarrow> rsimp (RALTS rs2) = rsimp (RALTS rs3)"
  apply(induct rs2 rs3 rule: frewrite.induct)
    apply simp
  using simp_flatten apply blast
  by (metis (no_types, opaque_lifting) list.simps(9) rsimp.simps(2) simp_flatten2)

lemma grewrite_simpalts:
  shows " rs2 \<leadsto>g rs3 \<Longrightarrow> rsimp (rsimp_ALTs rs2) = rsimp (rsimp_ALTs rs3)"
  apply(induct rs2 rs3 rule : grewrite.induct)
  using identity_wwo0 apply presburger
  apply (metis frewrite.intros(1) frewrite_single_step identity_wwo0 rsimp_ALTs.simps(3) simp_flatten)
  apply (smt (verit, ccfv_SIG) gmany_steps_later grewrites.intros(1) grewrites_cons grewrites_equal_rsimp identity_wwo0 rsimp_ALTs.simps(3))
  apply simp
  apply(subst rsimp_alts_equal)
  apply(case_tac "rsa = [] \<and> rsb = [] \<and> rsc = []")
   apply(subgoal_tac "rsa @ a # rsb @ rsc = [a]")
  apply (simp only:)
  apply (metis append_Nil frewrite.intros(1) frewrite_single_step identity_wwo0 rsimp_ALTs.simps(3) simp_removes_duplicate1(2))
   apply simp
  by (smt (verit, best) append.assoc append_Cons frewrite.intros(1) frewrite_single_step identity_wwo0 in_set_conv_decomp rsimp_ALTs.simps(3) simp_removes_duplicate3)


lemma grewrites_simpalts:
  shows " rs2 \<leadsto>g* rs3 \<Longrightarrow> rsimp (rsimp_ALTs rs2) = rsimp (rsimp_ALTs rs3)"
  apply(induct rs2 rs3 rule: grewrites.induct)
   apply simp
  using grewrite_simpalts by presburger


lemma simp_der_flts:
  shows "rsimp (RALTS (rdistinct (map (rder x) (rflts rs)) {})) = 
         rsimp (RALTS (rdistinct (rflts (map (rder x) rs)) {}))"
  apply(subgoal_tac "map (rder x) (rflts rs) \<leadsto>f* rflts (map (rder x) rs)")
  using frewrites_simpeq apply presburger
  using early_late_der_frewrites by auto


lemma simp_der_pierce_flts_prelim:
  shows "rsimp (rsimp_ALTs (rdistinct (map (rder x) (rflts rs)) {})) 
       = rsimp (rsimp_ALTs (rdistinct (rflts (map (rder x) rs)) {}))"
  by (metis append.right_neutral grewrite.intros(2) grewrite_simpalts rsimp_ALTs.simps(2) simp_der_flts)


lemma basic_regex_property1:
  shows "rnullable r \<Longrightarrow> rsimp r \<noteq> RZERO"
  apply(induct r rule: rsimp.induct)
  apply(auto)
  apply (metis idiot idiot2 rrexp.distinct(5))
  by (metis der_simp_nullability rnullable.simps(1) rnullable.simps(4) rsimp.simps(2))


lemma inside_simp_seq_nullable:
  shows 
"\<And>r1 r2.
       \<lbrakk>rsimp (rder x (rsimp r1)) = rsimp (rder x r1); rsimp (rder x (rsimp r2)) = rsimp (rder x r2);
        rnullable r1\<rbrakk>
       \<Longrightarrow> rsimp (rder x (rsimp_SEQ (rsimp r1) (rsimp r2))) =
           rsimp_ALTs (rdistinct (rflts [rsimp_SEQ (rsimp (rder x r1)) (rsimp r2), rsimp (rder x r2)]) {})"
  apply(case_tac "rsimp r1 = RONE")
   apply(simp)
  apply(subst basic_rsimp_SEQ_property1)
   apply (simp add: idem_after_simp1)
  apply(case_tac "rsimp r1 = RZERO")
  
  using basic_regex_property1 apply blast
  apply(case_tac "rsimp r2 = RZERO")
  
  apply (simp add: basic_rsimp_SEQ_property3)
  apply(subst idiot2)
     apply simp+
  apply(subgoal_tac "rnullable (rsimp r1)")
   apply simp
  using rsimp_idem apply presburger
  using der_simp_nullability by presburger
  


lemma grewrite_ralts:
  shows "rs \<leadsto>g rs' \<Longrightarrow> RALTS rs h\<leadsto>* RALTS rs'"
  by (smt (verit) grewrite_cases_middle hr_in_rstar hrewrite.intros(11) hrewrite.intros(7) hrewrite.intros(8))

lemma grewrites_ralts:
  shows "rs \<leadsto>g* rs' \<Longrightarrow> RALTS rs h\<leadsto>* RALTS rs'"
  apply(induct rule: grewrites.induct)
  apply simp
  using grewrite_ralts hreal_trans by blast
  

lemma distinct_grewrites_subgoal1:
  shows "  
       \<lbrakk>rs1 \<leadsto>g* [a]; RALTS rs1 h\<leadsto>* a; [a] \<leadsto>g rs3\<rbrakk> \<Longrightarrow> RALTS rs1 h\<leadsto>* rsimp_ALTs rs3"
  apply(subgoal_tac "RALTS rs1 h\<leadsto>* RALTS rs3")
  apply (metis hrewrite.intros(10) hrewrite.intros(9) rs2 rsimp_ALTs.cases rsimp_ALTs.simps(1) rsimp_ALTs.simps(2) rsimp_ALTs.simps(3))
  apply(subgoal_tac "rs1 \<leadsto>g* rs3")
  using grewrites_ralts apply blast
  using grewrites.intros(2) by presburger

lemma grewrites_ralts_rsimpalts:
  shows "rs \<leadsto>g* rs' \<Longrightarrow> RALTS rs h\<leadsto>* rsimp_ALTs rs' "
  apply(induct rs rs' rule: grewrites.induct)
   apply(case_tac rs)
  using hrewrite.intros(9) apply force
   apply(case_tac list)
  apply simp
  using hr_in_rstar hrewrite.intros(10) rsimp_ALTs.simps(2) apply presburger
   apply simp
  apply(case_tac rs2)
   apply simp
   apply (metis grewrite.intros(3) grewrite_singleton rsimp_ALTs.simps(1))
  apply(case_tac list)
   apply(simp)
  using distinct_grewrites_subgoal1 apply blast
  apply simp
  apply(case_tac rs3)
   apply simp
  using grewrites_ralts hrewrite.intros(9) apply blast
  by (metis (no_types, opaque_lifting) grewrite_ralts hr_in_rstar hreal_trans hrewrite.intros(10) neq_Nil_conv rsimp_ALTs.simps(2) rsimp_ALTs.simps(3))

lemma hrewrites_alts:
  shows " r h\<leadsto>* r' \<Longrightarrow> (RALTS (rs1 @ [r] @ rs2)) h\<leadsto>* (RALTS  (rs1 @ [r'] @ rs2))"
  apply(induct r r' rule: hrewrites.induct)
  apply simp
  using hrewrite.intros(6) by blast

inductive 
  srewritescf:: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> bool" (" _ scf\<leadsto>* _" [100, 100] 100)
where
  ss1: "[] scf\<leadsto>* []"
| ss2: "\<lbrakk>r h\<leadsto>* r'; rs scf\<leadsto>* rs'\<rbrakk> \<Longrightarrow> (r#rs) scf\<leadsto>* (r'#rs')"


lemma srewritescf_alt: "rs1 scf\<leadsto>* rs2 \<Longrightarrow> (RALTS (rs@rs1)) h\<leadsto>* (RALTS (rs@rs2))"

  apply(induct rs1 rs2 arbitrary: rs rule: srewritescf.induct)
   apply(rule rs1)
  apply(drule_tac x = "rsa@[r']" in meta_spec)
  apply simp
  apply(rule hreal_trans)
   prefer 2
   apply(assumption)
  apply(drule hrewrites_alts)
  by auto


corollary srewritescf_alt1: 
  assumes "rs1 scf\<leadsto>* rs2"
  shows "RALTS rs1 h\<leadsto>* RALTS rs2"
  using assms
  by (metis append_Nil srewritescf_alt)




lemma trivialrsimp_srewrites: 
  "\<lbrakk>\<And>x. x \<in> set rs \<Longrightarrow> x h\<leadsto>* f x \<rbrakk> \<Longrightarrow> rs scf\<leadsto>* (map f rs)"

  apply(induction rs)
   apply simp
   apply(rule ss1)
  by (metis insert_iff list.simps(15) list.simps(9) srewritescf.simps)

lemma hrewrites_list: 
  shows
" (\<And>xa. xa \<in> set x \<Longrightarrow> xa h\<leadsto>* rsimp xa) \<Longrightarrow> RALTS x h\<leadsto>* RALTS (map rsimp x)"
  apply(induct x)
   apply(simp)+
  by (simp add: srewritescf_alt1 ss2 trivialrsimp_srewrites)
(*  apply(subgoal_tac "RALTS x h\<leadsto>* RALTS (map rsimp x)")*)

  
lemma hrewrite_simpeq:
  shows "r1 h\<leadsto> r2 \<Longrightarrow> rsimp r1 = rsimp r2"
  apply(induct rule: hrewrite.induct)
            apply simp+
  apply (simp add: basic_rsimp_SEQ_property3)
  apply (simp add: basic_rsimp_SEQ_property1)
  using rsimp.simps(1) apply presburger
        apply simp+
  using flts_middle0 apply force

  
  using simp_flatten3 apply presburger

  apply simp+
  apply (simp add: idem_after_simp1)
  using grewrite.intros(4) grewrite_equal_rsimp by presburger

lemma hrewrites_simpeq:
  shows "r1 h\<leadsto>* r2 \<Longrightarrow> rsimp r1 = rsimp r2"
  apply(induct rule: hrewrites.induct)
   apply simp
  apply(subgoal_tac "rsimp r2 = rsimp r3")
   apply auto[1]
  using hrewrite_simpeq by presburger
  


lemma simp_hrewrites:
  shows "r1 h\<leadsto>* rsimp r1"
  apply(induct r1)
       apply simp+
    apply(case_tac "rsimp r11 = RONE")
     apply simp
     apply(subst basic_rsimp_SEQ_property1)
  apply(subgoal_tac "RSEQ r11 r12 h\<leadsto>* RSEQ RONE r12")
  using hreal_trans hrewrite.intros(3) apply blast
  using hrewrites_seq_context apply presburger
    apply(case_tac "rsimp r11 = RZERO")
     apply simp
  using hrewrite.intros(1) hrewrites_seq_context apply blast
    apply(case_tac "rsimp r12 = RZERO")
     apply simp
  apply(subst basic_rsimp_SEQ_property3)
  apply (meson hrewrite.intros(2) hrewrites.simps hrewrites_seq_context2)
    apply(subst idiot2)
       apply simp+
  using hrewrites_seq_contexts apply presburger
   apply simp
   apply(subgoal_tac "RALTS x h\<leadsto>* RALTS (map rsimp x)")
  apply(subgoal_tac "RALTS (map rsimp x) h\<leadsto>* rsimp_ALTs (rdistinct (rflts (map rsimp x)) {}) ")
  using hreal_trans apply blast
    apply (meson flts_gstar greal_trans grewrites_ralts_rsimpalts gstar_rdistinct)

   apply (simp add: grewrites_ralts hrewrites_list)
  by simp

lemma interleave_aux1:
  shows " RALT (RSEQ RZERO r1) r h\<leadsto>*  r"
  apply(subgoal_tac "RSEQ RZERO r1 h\<leadsto>* RZERO")
  apply(subgoal_tac "RALT (RSEQ RZERO r1) r h\<leadsto>* RALT RZERO r")
  apply (meson grewrite.intros(1) grewrite_ralts hreal_trans hrewrite.intros(10) hrewrites.simps)
  using rs1 srewritescf_alt1 ss1 ss2 apply presburger
  by (simp add: hr_in_rstar hrewrite.intros(1))



lemma rnullable_hrewrite:
  shows "r1 h\<leadsto> r2 \<Longrightarrow> rnullable r1 = rnullable r2"
  apply(induct rule: hrewrite.induct)
            apply simp+
     apply blast
    apply simp+
  done


lemma interleave1:
  shows "r h\<leadsto> r' \<Longrightarrow> rder c r h\<leadsto>* rder c r'"
  apply(induct r r' rule: hrewrite.induct)
            apply (simp add: hr_in_rstar hrewrite.intros(1))
  apply (metis (no_types, lifting) basic_rsimp_SEQ_property3 list.simps(8) list.simps(9) rder.simps(1) rder.simps(5) rdistinct.simps(1) rflts.simps(1) rflts.simps(2) rsimp.simps(1) rsimp.simps(2) rsimp.simps(3) rsimp_ALTs.simps(1) simp_hrewrites)
          apply simp
          apply(subst interleave_aux1)
          apply simp
         apply(case_tac "rnullable r1")
          apply simp
  
          apply (simp add: hrewrites_seq_context rnullable_hrewrite srewritescf_alt1 ss1 ss2)
  
         apply (simp add: hrewrites_seq_context rnullable_hrewrite)
        apply(case_tac "rnullable r1")
  apply simp
  
  using hr_in_rstar hrewrites_seq_context2 srewritescf_alt1 ss1 ss2 apply presburger
  apply simp
  using hr_in_rstar hrewrites_seq_context2 apply blast
       apply simp
  
  using hrewrites_alts apply auto[1]
  apply simp
  using grewrite.intros(1) grewrite_append grewrite_ralts apply auto[1]
  apply simp
  apply (simp add: grewrite.intros(2) grewrite_append grewrite_ralts)
  apply (simp add: hr_in_rstar hrewrite.intros(9))
   apply (simp add: hr_in_rstar hrewrite.intros(10))
  apply simp
  using hrewrite.intros(11) by auto

lemma interleave_star1:
  shows "r h\<leadsto>* r' \<Longrightarrow> rder c r h\<leadsto>* rder c r'"
  apply(induct rule : hrewrites.induct)
   apply simp
  by (meson hreal_trans interleave1)



lemma inside_simp_removal:
  shows " rsimp (rder x (rsimp r)) = rsimp (rder x r)"
  apply(induct r)
       apply simp+
    apply(case_tac "rnullable r1")
     apply simp
  
  using inside_simp_seq_nullable apply blast
    apply simp
  apply (smt (verit, del_insts) idiot2 basic_rsimp_SEQ_property3 der_simp_nullability rder.simps(1) rder.simps(5) rnullable.simps(2) rsimp.simps(1) rsimp_SEQ.simps(1) rsimp_idem)
   apply(subgoal_tac "rder x (RALTS xa) h\<leadsto>* rder x (rsimp (RALTS xa))")
  using hrewrites_simpeq apply presburger
  using interleave_star1 simp_hrewrites apply presburger
  by simp
  



lemma rders_simp_same_simpders:
  shows "s \<noteq> [] \<Longrightarrow> rders_simp r s = rsimp (rders r s)"
  apply(induct s rule: rev_induct)
   apply simp
  apply(case_tac "xs = []")
   apply simp
  apply(simp add: rders_append rders_simp_append)
  using inside_simp_removal by blast




lemma distinct_der:
  shows "rsimp (rsimp_ALTs (map (rder x) (rdistinct rs {}))) = 
         rsimp (rsimp_ALTs (rdistinct (map (rder x) rs) {}))"
  by (metis grewrites_simpalts gstar_rdistinct inside_simp_removal rder_rsimp_ALTs_commute)


  


lemma rders_simp_lambda:
  shows " rsimp \<circ> rder x \<circ> (\<lambda>r. rders_simp r xs) = (\<lambda>r. rders_simp r (xs @ [x]))"
  using rders_simp_append by auto

lemma rders_simp_nonempty_simped:
  shows "xs \<noteq> [] \<Longrightarrow> rsimp \<circ> (\<lambda>r. rders_simp r xs) = (\<lambda>r. rders_simp r xs)"
  using rders_simp_same_simpders rsimp_idem by auto

lemma repeated_altssimp:
  shows "\<forall>r \<in> set rs. rsimp r = r \<Longrightarrow> rsimp (rsimp_ALTs (rdistinct (rflts rs) {})) =
           rsimp_ALTs (rdistinct (rflts rs) {})"
  by (metis map_idI rsimp.simps(2) rsimp_idem)



lemma alts_closed_form: shows 
"rsimp (rders_simp (RALTS rs) s) = 
rsimp (RALTS (map (\<lambda>r. rders_simp r s) rs))"
  apply(induct s rule: rev_induct)
   apply simp
  apply simp
  apply(subst rders_simp_append)
  apply(subgoal_tac " rsimp (rders_simp (rders_simp (RALTS rs) xs) [x]) = 
 rsimp(rders_simp (rsimp_ALTs (rdistinct (rflts (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs)) {})) [x])")
   prefer 2
  apply (metis inside_simp_removal rders_simp_one_char)
  apply(simp only: )
  apply(subst rders_simp_one_char)
  apply(subst rsimp_idem)
  apply(subgoal_tac "rsimp (rder x (rsimp_ALTs (rdistinct (rflts (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs)) {}))) =
                     rsimp ((rsimp_ALTs (map (rder x) (rdistinct (rflts (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs)) {})))) ")
  prefer 2
  using rder_rsimp_ALTs_commute apply presburger
  apply(simp only:)
  apply(subgoal_tac "rsimp (rsimp_ALTs (map (rder x) (rdistinct (rflts (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs)) {})))
= rsimp (rsimp_ALTs (rdistinct (map (rder x) (rflts (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs))) {}))")
   prefer 2
  
  using distinct_der apply presburger
  apply(simp only:)
  apply(subgoal_tac " rsimp (rsimp_ALTs (rdistinct (map (rder x) (rflts (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs))) {})) =
                      rsimp (rsimp_ALTs (rdistinct ( (rflts (map (rder x) (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs)))) {}))")
   apply(simp only:)
  apply(subgoal_tac " rsimp (rsimp_ALTs (rdistinct (rflts (map (rder x) (map (rsimp \<circ> (\<lambda>r. rders_simp r xs)) rs))) {})) = 
                      rsimp (rsimp_ALTs (rdistinct (rflts ( (map (rsimp \<circ> (rder x) \<circ> (\<lambda>r. rders_simp r xs)) rs))) {}))")
    apply(simp only:)
  apply(subst rders_simp_lambda)
    apply(subst rders_simp_nonempty_simped)
     apply simp
    apply(subgoal_tac "\<forall>r \<in> set  (map (\<lambda>r. rders_simp r (xs @ [x])) rs). rsimp r = r")
  prefer 2
     apply (simp add: rders_simp_same_simpders rsimp_idem)
    apply(subst repeated_altssimp)
     apply simp
  apply fastforce
   apply (metis inside_simp_removal list.map_comp rder.simps(4) rsimp.simps(2) rsimp_idem)
  using simp_der_pierce_flts_prelim by blast

lemma alts_closed_form_variant: shows 
"s \<noteq> [] \<Longrightarrow> rders_simp (RALTS rs) s = 
rsimp (RALTS (map (\<lambda>r. rders_simp r s) rs))"
  by (metis alts_closed_form comp_apply rders_simp_nonempty_simped)


lemma rsimp_seq_equal1:
  shows "rsimp_SEQ (rsimp r1) (rsimp r2) = rsimp_ALTs (rdistinct (rflts [rsimp_SEQ (rsimp r1) (rsimp r2)]) {})"
  by (metis idem_after_simp1 rsimp.simps(1))


fun sflat_aux :: "rrexp  \<Rightarrow> rrexp list " where
  "sflat_aux (RALTS (r # rs)) = sflat_aux r @ rs"
| "sflat_aux (RALTS []) = []"
| "sflat_aux r = [r]"


fun sflat :: "rrexp \<Rightarrow> rrexp" where
  "sflat (RALTS (r # [])) = r"
| "sflat (RALTS (r # rs)) = RALTS (sflat_aux r @ rs)"
| "sflat r = r"

inductive created_by_seq:: "rrexp \<Rightarrow> bool" where
  "created_by_seq (RSEQ r1 r2) "
| "created_by_seq r1 \<Longrightarrow> created_by_seq (RALT r1 r2)"

lemma seq_ders_shape1:
  shows "\<forall>r1 r2. \<exists>r3 r4. (rders (RSEQ r1 r2) s) = RSEQ r3 r4 \<or> (rders (RSEQ r1 r2) s) = RALT r3 r4"
  apply(induct s rule: rev_induct)
   apply auto[1]
  apply(rule allI)+
  apply(subst rders_append)+
  apply(subgoal_tac " \<exists>r3 r4. rders (RSEQ r1 r2) xs = RSEQ r3 r4 \<or> rders (RSEQ r1 r2) xs = RALT r3 r4 ")
   apply(erule exE)+
   apply(erule disjE)
    apply simp+
  done

lemma created_by_seq_der:
  shows "created_by_seq r \<Longrightarrow> created_by_seq (rder c r)"
  apply(induct r)
  apply simp+
  
  using created_by_seq.cases apply blast
  
  apply (meson created_by_seq.cases rrexp.distinct(19) rrexp.distinct(21))
  apply (metis created_by_seq.simps rder.simps(5))
   apply (smt (verit, ccfv_threshold) created_by_seq.simps list.set_intros(1) list.simps(8) list.simps(9) rder.simps(4) rrexp.distinct(25) rrexp.inject(3))
  using created_by_seq.intros(1) by force

lemma createdbyseq_left_creatable:
  shows "created_by_seq (RALT r1 r2) \<Longrightarrow> created_by_seq r1"
  using created_by_seq.cases by blast



lemma recursively_derseq:
  shows " created_by_seq (rders (RSEQ r1 r2) s)"
  apply(induct s rule: rev_induct)
   apply simp
  using created_by_seq.intros(1) apply force
  apply(subgoal_tac "created_by_seq (rders (RSEQ r1 r2) (xs @ [x]))")
  apply blast
  apply(subst rders_append)
  apply(subgoal_tac "\<exists>r3 r4. rders (RSEQ r1 r2) xs = RSEQ r3 r4 \<or> 
                    rders (RSEQ r1 r2) xs = RALT r3 r4")
   prefer 2
  using seq_ders_shape1 apply presburger
  apply(erule exE)+
  apply(erule disjE)
   apply(subgoal_tac "created_by_seq (rders (RSEQ r3 r4) [x])")
    apply presburger
  apply simp
  using created_by_seq.intros(1) created_by_seq.intros(2) apply presburger
  apply simp
  apply(subgoal_tac "created_by_seq r3")
  prefer 2
  using createdbyseq_left_creatable apply blast
  using created_by_seq.intros(2) created_by_seq_der by blast

  
lemma recursively_derseq1:
  shows "r = rders (RSEQ r1 r2) s \<Longrightarrow> created_by_seq r"
  using recursively_derseq by blast


lemma sfau_head:
  shows " created_by_seq r \<Longrightarrow> \<exists>ra rb rs. sflat_aux r = RSEQ ra rb # rs"
  apply(induction r rule: created_by_seq.induct)
  apply simp
  by fastforce


lemma vsuf_prop1:
  shows "vsuf (xs @ [x]) r = (if (rnullable (rders r xs)) 
                                then [x] # (map (\<lambda>s. s @ [x]) (vsuf xs r) )
                                else (map (\<lambda>s. s @ [x]) (vsuf xs r)) ) 
             "
  apply(induct xs arbitrary: r)
   apply simp
  apply(case_tac "rnullable r")
  apply simp
  apply simp
  done

fun  breakHead :: "rrexp list \<Rightarrow> rrexp list" where
  "breakHead [] = [] "
| "breakHead (RALT r1 r2 # rs) = r1 # r2 # rs"
| "breakHead (r # rs) = r # rs"


lemma sfau_idem_der:
  shows "created_by_seq r \<Longrightarrow> sflat_aux (rder c r) = breakHead (map (rder c) (sflat_aux r))"
  apply(induct rule: created_by_seq.induct)
   apply simp+
  using sfau_head by fastforce

lemma vsuf_compose1:
  shows " \<not> rnullable (rders r1 xs)
       \<Longrightarrow> map (rder x \<circ> rders r2) (vsuf xs r1) = map (rders r2) (vsuf (xs @ [x]) r1)"
  apply(subst vsuf_prop1)
  apply simp
  by (simp add: rders_append)
  



lemma seq_sfau0:
  shows  "sflat_aux (rders (RSEQ r1 r2) s) = (RSEQ (rders r1 s) r2) #
                                       (map (rders r2) (vsuf s r1)) "
  apply(induct s rule: rev_induct)
   apply simp
  apply(subst rders_append)+
  apply(subgoal_tac "created_by_seq (rders (RSEQ r1 r2) xs)")
  prefer 2
  using recursively_derseq1 apply blast
  apply simp
  apply(subst sfau_idem_der)
  
   apply blast
  apply(case_tac "rnullable (rders r1 xs)")
   apply simp
   apply(subst vsuf_prop1)
  apply simp
  apply (simp add: rders_append)
  apply simp
  using vsuf_compose1 by blast









thm sflat.elims





lemma sflat_rsimpeq:
  shows "created_by_seq r1 \<Longrightarrow> sflat_aux r1 =  rs \<Longrightarrow> rsimp r1 = rsimp (RALTS rs)"
  apply(induct r1 arbitrary: rs rule:  created_by_seq.induct)
   apply simp
  using rsimp_seq_equal1 apply force
  by (metis head_one_more_simp rsimp.simps(2) sflat_aux.simps(1) simp_flatten)



lemma seq_closed_form_general:
  shows "rsimp (rders (RSEQ r1 r2) s) = 
rsimp ( (RALTS ( (RSEQ (rders r1 s) r2 # (map (rders r2) (vsuf s r1))))))"
  apply(case_tac "s \<noteq> []")
  apply(subgoal_tac "created_by_seq (rders (RSEQ r1 r2) s)")
  apply(subgoal_tac "sflat_aux (rders (RSEQ r1 r2) s) = RSEQ (rders r1 s) r2 # (map (rders r2) (vsuf s r1))")
  using sflat_rsimpeq apply blast
    apply (simp add: seq_sfau0)
  using recursively_derseq1 apply blast
  apply simp
  by (metis idem_after_simp1 rsimp.simps(1))
  


lemma seq_closed_form_aux1:
  shows "rsimp ( (RALTS ( (RSEQ (rders r1 s) r2 # (map (rders r2) (vsuf s r1)))))) =
rsimp ( (RALTS ( (RSEQ (rders_simp r1 s) r2 # (map (rders r2) (vsuf s r1))))))"
  by (smt (verit, best) list.simps(9) rders.simps(1) rders_simp.simps(1) rders_simp_same_simpders rsimp.simps(1) rsimp.simps(2) rsimp_idem)

lemma add_simp_to_rest:
  shows "rsimp (RALTS (r # rs)) = rsimp (RALTS (r # map rsimp rs))"
  by (metis append_Nil2 grewrite.intros(2) grewrite_simpalts head_one_more_simp list.simps(9) rsimp_ALTs.simps(2) spawn_simp_rsimpalts)

lemma rsimp_compose_der2:
  shows "\<forall>s \<in> set ss. s \<noteq> [] \<Longrightarrow> map rsimp (map (rders r) ss) = map (\<lambda>s.  (rders_simp r s)) ss"  
  by (simp add: rders_simp_same_simpders)

lemma vsuf_nonempty:
  shows "\<forall>s \<in> set ( vsuf s1 r). s \<noteq> []"
  apply(induct s1 arbitrary: r)
   apply simp
  apply simp
  done



lemma seq_closed_form_aux2:
  shows "s \<noteq> [] \<Longrightarrow> rsimp ( (RALTS ( (RSEQ (rders_simp r1 s) r2 # (map (rders r2) (vsuf s r1)))))) = 
         rsimp ( (RALTS ( (RSEQ (rders_simp r1 s) r2 # (map (rders_simp r2) (vsuf s r1))))))"
  
  by (metis add_simp_to_rest rsimp_compose_der2 vsuf_nonempty)
  

lemma seq_closed_form: shows 
"rsimp (rders_simp (RSEQ r1 r2) s) = 
rsimp ( RALTS ( (RSEQ (rders_simp r1 s) r2) # 
                (map (rders_simp r2) (vsuf s r1)) 
              )  
      )"
  apply(case_tac s )
   apply simp  
  apply (metis idem_after_simp1 rsimp.simps(1))
  apply(subgoal_tac " s \<noteq> []")
  using rders_simp_same_simpders rsimp_idem seq_closed_form_aux1 seq_closed_form_aux2 seq_closed_form_general apply presburger
  by fastforce
  




lemma seq_closed_form_variant: shows
"s \<noteq> [] \<Longrightarrow> (rders_simp (RSEQ r1 r2) s) = 
rsimp (RALTS ((RSEQ (rders_simp r1 s) r2) # (map (rders_simp r2) (vsuf s r1))))"
  apply(induct s rule: rev_induct)
   apply simp
  apply(subst rders_simp_append)
  apply(subst rders_simp_one_char)
  apply(subst rsimp_idem[symmetric])
  apply(subst rders_simp_one_char[symmetric])
  apply(subst rders_simp_append[symmetric])
  apply(insert seq_closed_form)
  apply(subgoal_tac "rsimp (rders_simp (RSEQ r1 r2) (xs @ [x]))
 = rsimp (RALTS (RSEQ (rders_simp r1 (xs @ [x])) r2 # map (rders_simp r2) (vsuf (xs @ [x]) r1)))")
   apply force
  by presburger


fun hflat_aux :: "rrexp \<Rightarrow> rrexp list" where
  "hflat_aux (RALT r1 r2) = hflat_aux r1 @ hflat_aux r2"
| "hflat_aux r = [r]"


fun hflat :: "rrexp \<Rightarrow> rrexp" where
  "hflat (RALT r1 r2) = RALTS ((hflat_aux r1) @ (hflat_aux r2))"
| "hflat r = r"

inductive created_by_star :: "rrexp \<Rightarrow> bool" where
  "created_by_star (RSEQ ra (RSTAR rb))"
| "\<lbrakk>created_by_star r1; created_by_star r2\<rbrakk> \<Longrightarrow> created_by_star (RALT r1 r2)"

fun hElem :: "rrexp  \<Rightarrow> rrexp list" where
  "hElem (RALT r1 r2) = (hElem r1 ) @ (hElem r2)"
| "hElem r = [r]"




lemma cbs_ders_cbs:
  shows "created_by_star r \<Longrightarrow> created_by_star (rder c r)"
  apply(induct r rule: created_by_star.induct)
   apply simp
  using created_by_star.intros(1) created_by_star.intros(2) apply auto[1]
  by (metis (mono_tags, lifting) created_by_star.simps list.simps(8) list.simps(9) rder.simps(4))

lemma star_ders_cbs:
  shows "created_by_star (rders (RSEQ r1 (RSTAR r2)) s)"
  apply(induct s rule: rev_induct)
   apply simp
   apply (simp add: created_by_star.intros(1))
  apply(subst rders_append)
  apply simp
  using cbs_ders_cbs by auto

(*
lemma created_by_star_cases:
  shows "created_by_star r \<Longrightarrow> \<exists>ra rb. (r = RALT ra rb \<and> created_by_star ra \<and> created_by_star rb) \<or> r = RSEQ ra rb "
  by (meson created_by_star.cases)
*)


lemma hfau_pushin: 
  shows "created_by_star r \<Longrightarrow> hflat_aux (rder c r) = concat (map hElem (map (rder c) (hflat_aux r)))"
  apply(induct r rule: created_by_star.induct)
   apply simp
  apply(subgoal_tac "created_by_star (rder c r1)")
  prefer 2
  apply(subgoal_tac "created_by_star (rder c r2)")
  using cbs_ders_cbs apply blast
  using cbs_ders_cbs apply auto[1]
  apply simp
  done

lemma stupdate_induct1:
  shows " concat (map (hElem \<circ> (rder x \<circ> (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0)))) Ss) =
          map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0)) (star_update x r0 Ss)"
  apply(induct Ss)
   apply simp+
  by (simp add: rders_append)
  


lemma stupdates_join_general:
  shows  "concat (map hElem (map (rder x) (map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0)) (star_updates xs r0 Ss)))) =
           map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0)) (star_updates (xs @ [x]) r0 Ss)"
  apply(induct xs arbitrary: Ss)
   apply (simp)
  prefer 2
   apply auto[1]
  using stupdate_induct1 by blast

lemma star_hfau_induct:
  shows "hflat_aux (rders (RSEQ (rder c r0) (RSTAR r0)) s) =   
      map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0)) (star_updates s r0 [[c]])"
  apply(induct s rule: rev_induct)
   apply simp
  apply(subst rders_append)+
  apply simp
  apply(subst stupdates_append)
  apply(subgoal_tac "created_by_star (rders (RSEQ (rder c r0) (RSTAR r0)) xs)")
  prefer 2
  apply (simp add: star_ders_cbs)
  apply(subst hfau_pushin)
   apply simp
  apply(subgoal_tac "concat (map hElem (map (rder x) (hflat_aux (rders (RSEQ (rder c r0) (RSTAR r0)) xs)))) =
                     concat (map hElem (map (rder x) ( map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0)) (star_updates xs r0 [[c]])))) ")
   apply(simp only:)
  prefer 2
   apply presburger
  apply(subst stupdates_append[symmetric])
  using stupdates_join_general by blast

lemma starders_hfau_also1:
  shows "hflat_aux (rders (RSTAR r) (c # xs)) = map (\<lambda>s1. RSEQ (rders r s1) (RSTAR r)) (star_updates xs r [[c]])"
  using star_hfau_induct by force

lemma hflat_aux_grewrites:
  shows "a # rs \<leadsto>g* hflat_aux a @ rs"
  apply(induct a arbitrary: rs)
       apply simp+
   apply(case_tac x)
    apply simp
  apply(case_tac list)
  
  apply (metis append.right_neutral append_Cons append_eq_append_conv2 grewrites.simps hflat_aux.simps(7) same_append_eq)
   apply(case_tac lista)
  apply simp
  apply (metis (no_types, lifting) append_Cons append_eq_append_conv2 gmany_steps_later greal_trans grewrite.intros(2) grewrites_append self_append_conv)
  apply simp
  by simp
  



lemma cbs_hfau_rsimpeq1:
  shows "rsimp (RALT a b) = rsimp (RALTS ((hflat_aux a) @ (hflat_aux b)))"
  apply(subgoal_tac "[a, b] \<leadsto>g* hflat_aux a @ hflat_aux b")
  using grewrites_equal_rsimp apply presburger
  by (metis append.right_neutral greal_trans grewrites_cons hflat_aux_grewrites)


lemma hfau_rsimpeq2:
  shows "created_by_star r \<Longrightarrow> rsimp r = rsimp ( (RALTS (hflat_aux r)))"
  apply(induct r)
       apply simp+
  
    apply (metis rsimp_seq_equal1)
  prefer 2
   apply simp
  apply(case_tac x)
   apply simp
  apply(case_tac "list")
   apply simp
  
  apply (metis idem_after_simp1)
  apply(case_tac "lista")
  prefer 2
   apply (metis hflat_aux.simps(8) idem_after_simp1 list.simps(8) list.simps(9) rsimp.simps(2))
  apply(subgoal_tac "rsimp (RALT a aa) = rsimp (RALTS (hflat_aux (RALT a aa)))")
  apply simp
  apply(subgoal_tac "rsimp (RALT a aa) = rsimp (RALTS (hflat_aux a @ hflat_aux aa))")
  using hflat_aux.simps(1) apply presburger
  apply simp
  using cbs_hfau_rsimpeq1 by fastforce

lemma star_closed_form1:
  shows "rsimp (rders (RSTAR r0) (c#s)) = 
rsimp ( ( RALTS ( (map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0) ) (star_updates s r0 [[c]]) ) )))"
  using hfau_rsimpeq2 rder.simps(6) rders.simps(2) star_ders_cbs starders_hfau_also1 by presburger

lemma star_closed_form2:
  shows  "rsimp (rders_simp (RSTAR r0) (c#s)) = 
rsimp ( ( RALTS ( (map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0) ) (star_updates s r0 [[c]]) ) )))"
  by (metis list.distinct(1) rders_simp_same_simpders rsimp_idem star_closed_form1)

lemma star_closed_form3:
  shows  "rsimp (rders_simp (RSTAR r0) (c#s)) =   (rders_simp (RSTAR r0) (c#s))"
  by (metis list.distinct(1) rders_simp_same_simpders star_closed_form1 star_closed_form2)

lemma star_closed_form4:
  shows " (rders_simp (RSTAR r0) (c#s)) = 
rsimp ( ( RALTS ( (map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0) ) (star_updates s r0 [[c]]) ) )))"
  using star_closed_form2 star_closed_form3 by presburger

lemma star_closed_form5:
  shows " rsimp ( ( RALTS ( (map (\<lambda>s1. RSEQ (rders r0 s1) (RSTAR r0) ) Ss         )))) = 
          rsimp ( ( RALTS ( (map (\<lambda>s1. rsimp (RSEQ (rders r0 s1) (RSTAR r0)) ) Ss ))))"
  by (metis (mono_tags, lifting) list.map_comp map_eq_conv o_apply rsimp.simps(2) rsimp_idem)

lemma star_closed_form6_hrewrites:
  shows "  
 (map (\<lambda>s1.  (RSEQ (rsimp (rders r0 s1)) (RSTAR r0)) ) Ss )
 scf\<leadsto>*
(map (\<lambda>s1. rsimp (RSEQ (rders r0 s1) (RSTAR r0)) ) Ss )"
  apply(induct Ss)
  apply simp
  apply (simp add: ss1)
  by (metis (no_types, lifting) list.simps(9) rsimp.simps(1) rsimp_idem simp_hrewrites ss2)

lemma star_closed_form6:
  shows " rsimp ( ( RALTS ( (map (\<lambda>s1. rsimp (RSEQ (rders r0 s1) (RSTAR r0)) ) Ss )))) = 
          rsimp ( ( RALTS ( (map (\<lambda>s1.  (RSEQ (rsimp (rders r0 s1)) (RSTAR r0)) ) Ss ))))"
  apply(subgoal_tac " map (\<lambda>s1.  (RSEQ (rsimp (rders r0 s1)) (RSTAR r0)) ) Ss  scf\<leadsto>*
                      map (\<lambda>s1.  rsimp (RSEQ  (rders r0 s1) (RSTAR r0)) ) Ss ")
  using hrewrites_simpeq srewritescf_alt1 apply fastforce
  using star_closed_form6_hrewrites by blast

lemma stupdate_nonempty:
  shows "\<forall>s \<in> set  Ss. s \<noteq> [] \<Longrightarrow> \<forall>s \<in> set (star_update c r Ss). s \<noteq> []"
  apply(induct Ss)
  apply simp
  apply(case_tac "rnullable (rders r a)")
   apply simp+
  done


lemma stupdates_nonempty:
  shows "\<forall>s \<in> set Ss. s\<noteq> [] \<Longrightarrow> \<forall>s \<in> set (star_updates s r Ss). s \<noteq> []"
  apply(induct s arbitrary: Ss)
   apply simp
  apply simp
  using stupdate_nonempty by presburger


lemma star_closed_form8:
  shows  
"rsimp ( ( RALTS ( (map (\<lambda>s1. RSEQ (rsimp (rders r0 s1)) (RSTAR r0) ) (star_updates s r0 [[c]]) ) ))) = 
 rsimp ( ( RALTS ( (map (\<lambda>s1. RSEQ ( (rders_simp r0 s1)) (RSTAR r0) ) (star_updates s r0 [[c]]) ) )))"
  by (smt (verit, ccfv_SIG) list.simps(8) map_eq_conv rders__onechar rders_simp_same_simpders set_ConsD stupdates_nonempty)


lemma star_closed_form:
  shows "rders_simp (RSTAR r0) (c#s) = 
rsimp ( RALTS ( (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0) ) (star_updates s r0 [[c]]) ) ))"
  apply(induct s)
   apply simp
   apply (metis idem_after_simp1 rsimp.simps(1) rsimp.simps(6) rsimp_idem)
  using star_closed_form4 star_closed_form5 star_closed_form6 star_closed_form8 by presburger


unused_thms

end
theory BasicIdentities imports 
"Lexer"  "PDerivs"
begin

datatype rrexp = 
  RZERO
| RONE 
| RCHAR char
| RSEQ rrexp rrexp
| RALTS "rrexp list"
| RSTAR rrexp

abbreviation
  "RALT r1 r2 \<equiv> RALTS [r1, r2]"



fun
 rnullable :: "rrexp \<Rightarrow> bool"
where
  "rnullable (RZERO) = False"
| "rnullable (RONE  ) = True"
| "rnullable (RCHAR   c) = False"
| "rnullable (RALTS   rs) = (\<exists>r \<in> set rs. rnullable r)"
| "rnullable (RSEQ  r1 r2) = (rnullable r1 \<and> rnullable r2)"
| "rnullable (RSTAR   r) = True"


fun
 rder :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp"
where
  "rder c (RZERO) = RZERO"
| "rder c (RONE) = RZERO"
| "rder c (RCHAR d) = (if c = d then RONE else RZERO)"
| "rder c (RALTS rs) = RALTS (map (rder c) rs)"
| "rder c (RSEQ r1 r2) = 
     (if rnullable r1
      then RALT   (RSEQ (rder c r1) r2) (rder c r2)
      else RSEQ   (rder c r1) r2)"
| "rder c (RSTAR r) = RSEQ  (rder c r) (RSTAR r)"


fun 
  rders :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp"
where
  "rders r [] = r"
| "rders r (c#s) = rders (rder c r) s"

fun rdistinct :: "'a list \<Rightarrow>'a set \<Rightarrow> 'a list"
  where
  "rdistinct [] acc = []"
| "rdistinct (x#xs)  acc = 
     (if x \<in> acc then rdistinct xs  acc 
      else x # (rdistinct xs  ({x} \<union> acc)))"

lemma rdistinct1:
  assumes "a \<in> acc"
  shows "a \<notin> set (rdistinct rs acc)"
  using assms
  apply(induct rs arbitrary: acc a)
   apply(auto)
  done


lemma rdistinct_does_the_job:
  shows "distinct (rdistinct rs s)"
  apply(induct rs arbitrary: s)
  apply simp
  apply simp
  apply(auto)
  by (simp add: rdistinct1)




lemma rdistinct_concat:
  shows "set rs \<subseteq> rset \<Longrightarrow> rdistinct (rs @ rsa) rset = rdistinct rsa rset"
  apply(induct rs)
   apply simp+
  done

lemma rdistinct_concat2:
  shows "\<forall>r \<in> set rs. r \<in> rset \<Longrightarrow> rdistinct (rs @ rsa) rset = rdistinct rsa rset"
  by (simp add: rdistinct_concat subsetI)


lemma distinct_not_exist:
  shows "a \<notin> set rs \<Longrightarrow> rdistinct rs rset = rdistinct rs (insert a rset)"
  apply(induct rs arbitrary: rset)
   apply simp
  apply(case_tac "aa \<in> rset")
   apply simp
  apply(subgoal_tac "a \<noteq> aa")
   prefer 2
  apply simp
  apply simp
  done

lemma rdistinct_on_distinct:
  shows "distinct rs \<Longrightarrow> rdistinct rs {} = rs"
  apply(induct rs)
   apply simp
  apply(subgoal_tac "rdistinct rs {} = rs")
   prefer 2
  apply simp
  using distinct_not_exist by fastforce


lemma distinct_rdistinct_append:
  assumes "distinct rs1" "\<forall>r \<in> set rs1. r \<notin> acc"
  shows "rdistinct (rs1 @ rsa) acc = rs1 @ (rdistinct rsa (acc \<union> set rs1))"
  using assms
  apply(induct rs1 arbitrary: rsa acc)
   apply(auto)[1]
  apply(auto)[1]
  apply(drule_tac x="rsa" in meta_spec)
  apply(drule_tac x="{a} \<union> acc" in meta_spec)
  apply(simp)
  apply(drule meta_mp)
   apply(auto)[1]
  apply(simp)
  done
  




lemma rdistinct_set_equality1:
  shows "set (rdistinct rs acc) = set rs - acc"
  apply(induct rs acc rule: rdistinct.induct)
   apply(auto)
  done

lemma rdistinct_set_equality:
  shows "set (rdistinct rs {}) = set rs"
  by (simp add: rdistinct_set_equality1)


fun rflts :: "rrexp list \<Rightarrow> rrexp list"
  where 
  "rflts [] = []"
| "rflts (RZERO # rs) = rflts rs"
| "rflts ((RALTS rs1) # rs) = rs1 @ rflts rs"
| "rflts (r1 # rs) = r1 # rflts rs"

lemma rflts_def_idiot:
  shows "\<lbrakk> a \<noteq> RZERO; \<nexists>rs1. a = RALTS rs1\<rbrakk>
       \<Longrightarrow> rflts (a # rs) = a # rflts rs"
  apply(case_tac a)
       apply simp_all
  done

lemma rflts_def_idiot2:
  shows "\<lbrakk>a \<noteq> RZERO; \<nexists>rs1. a = RALTS rs1; a \<in> set rs\<rbrakk> \<Longrightarrow> a \<in> set (rflts rs)"
  apply(induct rs)
   apply simp
  by (metis append.assoc in_set_conv_decomp insert_iff list.simps(15) rflts.simps(2) rflts.simps(3) rflts_def_idiot)



lemma flts_append:
  shows "rflts (rs1 @ rs2) = rflts rs1 @ rflts rs2"
  apply(induct rs1)
   apply simp
  apply(case_tac a)
       apply simp+
  done


fun rsimp_ALTs :: " rrexp list \<Rightarrow> rrexp"
  where
  "rsimp_ALTs  [] = RZERO"
| "rsimp_ALTs [r] =  r"
| "rsimp_ALTs rs = RALTS rs"

lemma rsimpalts_gte2elems:
  shows "size rlist \<ge> 2 \<Longrightarrow> rsimp_ALTs rlist = RALTS rlist"
  apply(induct rlist)
   apply simp
  apply(induct rlist)
   apply simp
  apply (metis Suc_le_length_iff rsimp_ALTs.simps(3))
  by blast

lemma rsimpalts_conscons:
  shows "rsimp_ALTs (r1 # rsa @ r2 # rsb) = RALTS (r1 # rsa @ r2 # rsb)"
  by (metis Nil_is_append_conv list.exhaust rsimp_ALTs.simps(3))

lemma rsimp_alts_equal:
  shows "rsimp_ALTs (rsa @ a # rsb @ a # rsc) = RALTS (rsa @ a # rsb @ a # rsc) "
  by (metis append_Cons append_Nil neq_Nil_conv rsimpalts_conscons)


fun rsimp_SEQ :: " rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp"
  where
  "rsimp_SEQ  RZERO _ = RZERO"
| "rsimp_SEQ  _ RZERO = RZERO"
| "rsimp_SEQ RONE r2 = r2"
| "rsimp_SEQ r1 r2 = RSEQ r1 r2"


fun rsimp :: "rrexp \<Rightarrow> rrexp" 
  where
  "rsimp (RSEQ r1 r2) = rsimp_SEQ  (rsimp r1) (rsimp r2)"
| "rsimp (RALTS rs) = rsimp_ALTs  (rdistinct (rflts (map rsimp rs))  {}) "
| "rsimp r = r"


fun 
  rders_simp :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp"
where
  "rders_simp r [] = r"
| "rders_simp r (c#s) = rders_simp (rsimp (rder c r)) s"

fun rsize :: "rrexp \<Rightarrow> nat" where
  "rsize RZERO = 1"
| "rsize (RONE) = 1" 
| "rsize (RCHAR  c) = 1"
| "rsize (RALTS  rs) = Suc (sum_list (map rsize rs))"
| "rsize (RSEQ  r1 r2) = Suc (rsize r1 + rsize r2)"
| "rsize (RSTAR  r) = Suc (rsize r)"


lemma rder_rsimp_ALTs_commute:
  shows "  (rder x (rsimp_ALTs rs)) = rsimp_ALTs (map (rder x) rs)"
  apply(induct rs)
   apply simp
  apply(case_tac rs)
   apply simp
  apply auto
  done


lemma rsimp_aalts_smaller:
  shows "rsize (rsimp_ALTs  rs) \<le> rsize (RALTS rs)"
  apply(induct rs)
   apply simp
  apply simp
  apply(case_tac "rs = []")
   apply simp
  apply(subgoal_tac "\<exists>rsp ap. rs = ap # rsp")
   apply(erule exE)+
   apply simp
  apply simp
  by(meson neq_Nil_conv)
  




lemma rSEQ_mono:
  shows "rsize (rsimp_SEQ r1 r2) \<le>rsize ( RSEQ r1 r2)"
  apply auto
  apply(induct r1)
       apply auto
      apply(case_tac "r2")
       apply simp_all
     apply(case_tac r2)
          apply simp_all
     apply(case_tac r2)
         apply simp_all
     apply(case_tac r2)
        apply simp_all
     apply(case_tac r2)
  apply simp_all
  done

lemma ralts_cap_mono:
  shows "rsize (RALTS rs) \<le> Suc ( sum_list (map rsize rs)) "
  by simp




lemma rflts_mono:
  shows "sum_list (map rsize (rflts rs))\<le> sum_list (map rsize rs)"
  apply(induct rs)
  apply simp
  apply(case_tac "a = RZERO")
   apply simp
  apply(case_tac "\<exists>rs1. a = RALTS rs1")
  apply(erule exE)
   apply simp
  apply(subgoal_tac "rflts (a # rs) = a # (rflts rs)")
  prefer 2
  using rflts_def_idiot apply blast
  apply simp
  done

lemma rdistinct_smaller: shows "sum_list (map rsize (rdistinct rs ss)) \<le>
sum_list (map rsize rs )"
  apply (induct rs arbitrary: ss)
   apply simp
  by (simp add: trans_le_add2)

lemma rdistinct_phi_smaller: "sum_list (map rsize (rdistinct rs {})) \<le> sum_list (map rsize rs)"
  by (simp add: rdistinct_smaller)


lemma rsimp_alts_mono :
  shows "\<And>x. (\<And>xa. xa \<in> set x \<Longrightarrow> rsize (rsimp xa) \<le> rsize xa)  \<Longrightarrow>
rsize (rsimp_ALTs (rdistinct (rflts (map rsimp x)) {})) \<le> Suc (sum_list (map rsize x))"
  apply(subgoal_tac "rsize (rsimp_ALTs (rdistinct (rflts (map rsimp x)) {} )) 
                    \<le> rsize (RALTS (rdistinct (rflts (map rsimp x)) {} ))")
  prefer 2
  using rsimp_aalts_smaller apply auto[1]
  apply(subgoal_tac "rsize (RALTS (rdistinct (rflts (map rsimp x)) {})) \<le>Suc( sum_list (map rsize (rdistinct (rflts (map rsimp x)) {})))")
  prefer 2
  using ralts_cap_mono apply blast
  apply(subgoal_tac "sum_list (map rsize (rdistinct (rflts (map rsimp x)) {})) \<le>
                     sum_list (map rsize ( (rflts (map rsimp x))))")
  prefer 2
  using rdistinct_smaller apply presburger
  apply(subgoal_tac "sum_list (map rsize (rflts (map rsimp x))) \<le> 
                     sum_list (map rsize (map rsimp x))")
  prefer 2
  using rflts_mono apply blast
  apply(subgoal_tac "sum_list (map rsize (map rsimp x)) \<le> sum_list (map rsize x)")
  prefer 2
  
  apply (simp add: sum_list_mono)
  by linarith





lemma rsimp_mono:
  shows "rsize (rsimp r) \<le> rsize r"
  apply(induct r)
  apply simp_all
  apply(subgoal_tac "rsize (rsimp_SEQ (rsimp r1) (rsimp r2)) \<le> rsize (RSEQ (rsimp r1) (rsimp r2))")
    apply force
  using rSEQ_mono
   apply presburger
  using rsimp_alts_mono by auto

lemma idiot:
  shows "rsimp_SEQ RONE r = r"
  apply(case_tac r)
       apply simp_all
  done





lemma idiot2:
  shows " \<lbrakk>r1 \<noteq> RZERO; r1 \<noteq> RONE;r2 \<noteq> RZERO\<rbrakk>
    \<Longrightarrow> rsimp_SEQ r1 r2 = RSEQ r1 r2"
  apply(case_tac r1)
       apply(case_tac r2)
  apply simp_all
     apply(case_tac r2)
  apply simp_all
     apply(case_tac r2)
  apply simp_all
   apply(case_tac r2)
  apply simp_all
  apply(case_tac r2)
       apply simp_all
  done

lemma rders__onechar:
  shows " (rders_simp r [c]) =  (rsimp (rders r [c]))"
  by simp

lemma rders_append:
  "rders c (s1 @ s2) = rders (rders c s1) s2"
  apply(induct s1 arbitrary: c s2)
  apply(simp_all)
  done

lemma rders_simp_append:
  "rders_simp c (s1 @ s2) = rders_simp (rders_simp c s1) s2"
  apply(induct s1 arbitrary: c s2)
   apply(simp_all)
  done



lemma set_related_list:
  shows "distinct rs  \<Longrightarrow> length rs = card (set rs)"
  by (simp add: distinct_card)
(*this section deals with the property of distinctBy: creates a list without duplicates*)
lemma rdistinct_never_added_twice:
  shows "rdistinct (a # rs) {a} = rdistinct rs {a}"
  by force







lemma rders_simp_one_char:
  shows "rders_simp r [c] = rsimp (rder c r)"
  apply auto
  done



fun nonalt :: "rrexp \<Rightarrow> bool"
  where
  "nonalt (RALTS  rs) = False"
| "nonalt r = True"


fun good :: "rrexp \<Rightarrow> bool" where
  "good RZERO = False"
| "good (RONE) = True" 
| "good (RCHAR c) = True"
| "good (RALTS []) = False"
| "good (RALTS [r]) = False"
| "good (RALTS (r1 # r2 # rs)) = ((distinct ( (r1 # r2 # rs))) \<and>(\<forall>r' \<in> set (r1 # r2 # rs). good r' \<and> nonalt r'))"
| "good (RSEQ RZERO _) = False"
| "good (RSEQ RONE _) = False"
| "good (RSEQ  _ RZERO) = False"
| "good (RSEQ r1 r2) = (good r1 \<and> good r2)"
| "good (RSTAR r) = True"


lemma  k0a:
  shows "rflts [RALTS rs] =   rs"
  apply(simp)
  done

lemma bbbbs:
  assumes "good r" "r = RALTS rs"
  shows "rsimp_ALTs  (rflts [r]) = RALTS rs"
  using  assms
  by (metis good.simps(4) good.simps(5) k0a rsimp_ALTs.elims)

lemma bbbbs1:
  shows "nonalt r \<or> (\<exists> rs. r  = RALTS  rs)"
  by (meson nonalt.elims(3))



lemma good0:
  assumes "rs \<noteq> Nil" "\<forall>r \<in> set rs. nonalt r" "distinct rs"
  shows "good (rsimp_ALTs rs) \<longleftrightarrow> (\<forall>r \<in> set rs. good r)"
  using  assms
  apply(induct  rs rule: rsimp_ALTs.induct)
  apply(auto)
  done

lemma good0a:
  assumes "rflts (map rsimp rs) \<noteq> Nil" "\<forall>r \<in> set (rflts (map rsimp rs)). nonalt r"
  shows "good (rsimp (RALTS rs)) \<longleftrightarrow> (\<forall>r \<in> set (rflts (map rsimp rs)). good r)"
  using  assms
  apply(simp)
  apply(auto)
   apply(subst (asm) good0)
  
  apply (metis rdistinct_set_equality set_empty)
   apply(simp)
    apply(auto)
     apply (metis rdistinct_set_equality)
  using rdistinct_does_the_job apply blast
  apply (metis rdistinct_set_equality)
  by (metis good0 rdistinct_does_the_job rdistinct_set_equality set_empty)


lemma flts0:
  assumes "r \<noteq> RZERO" "nonalt r"
  shows "rflts [r] \<noteq> []"
  using  assms
  apply(induct r)
       apply(simp_all)
  done

lemma flts1:
  assumes "good r" 
  shows "rflts [r] \<noteq> []"
  using  assms
  apply(induct r)
       apply(simp_all)
  using good.simps(4) by blast

lemma flts2:
  assumes "good r" 
  shows "\<forall>r' \<in> set (rflts [r]). good r' \<and> nonalt r'"
  using  assms
  apply(induct r)
       apply(simp)
      apply(simp)
     apply(simp)
    prefer 2
    apply(simp)
    apply(auto)[1]
  
     apply (metis flts1 good.simps(5) good.simps(6) k0a neq_Nil_conv)
    apply (metis flts1 good.simps(5) good.simps(6) k0a neq_Nil_conv)
   apply fastforce
  apply(simp)
  done  



lemma flts3:
  assumes "\<forall>r \<in> set rs. good r \<or> r = RZERO" 
  shows "\<forall>r \<in> set (rflts rs). good r"
  using  assms
  apply(induct rs arbitrary: rule: rflts.induct)
        apply(simp_all)
  by (metis UnE flts2 k0a)

lemma flts3b:
  assumes "\<exists>r\<in>set rs. good r"
  shows "rflts rs \<noteq> []"
  using  assms
  apply(induct rs arbitrary: rule: rflts.induct)
        apply(simp)
       apply(simp)
      apply(simp)
      apply(auto)
  done

lemma flts4:
  assumes "rsimp_ALTs (rflts rs) = RZERO"
  shows "\<forall>r \<in> set rs. \<not> good r"
  using assms
  apply(induct rs  rule: rflts.induct)
        apply(auto)
        defer
  apply (metis (no_types, lifting) Nil_is_append_conv append_self_conv2 rsimp_ALTs.elims butlast.simps(2) butlast_append flts3b nonalt.simps(1) nonalt.simps(2))
  using rsimp_ALTs.elims apply auto[1]
  using rsimp_ALTs.elims apply auto[1]
  using rsimp_ALTs.elims apply auto[1]
  using rsimp_ALTs.elims apply auto[1]
  using rsimp_ALTs.elims apply auto[1]
  by (smt (verit, del_insts) append_Cons append_is_Nil_conv bbbbs k0a list.inject rrexp.distinct(7) rsimp_ALTs.elims)


lemma  k0:
  shows "rflts (r # rs1) = rflts [r] @ rflts rs1"
  apply(induct r arbitrary: rs1)
   apply(auto)
  done

lemma flts_nil2:
  assumes "\<forall>y. rsize y < Suc (sum_list (map rsize rs)) \<longrightarrow>
            good (rsimp y) \<or> rsimp y = RZERO"
  and "rsimp_ALTs  (rflts (map rsimp rs)) = RZERO"
  shows "rflts (map rsimp rs) = []"
  using assms
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(subst k0)
  apply(simp)
  apply(subst (asm) k0)
  apply(auto)
  apply (metis rflts.simps(1) rflts.simps(2) flts4 k0 less_add_Suc1 list.set_intros(1))
  by (metis flts4 k0 less_add_Suc1 list.set_intros(1) rflts.simps(2))


lemma good_SEQ:
  assumes "r1 \<noteq> RZERO" "r2 \<noteq> RZERO" " r1 \<noteq> RONE"
  shows "good (RSEQ r1 r2) = (good r1 \<and> good r2)"
  using assms
  apply(case_tac r1)
       apply(simp_all)
  apply(case_tac r2)
          apply(simp_all)
  apply(case_tac r2)
         apply(simp_all)
  apply(case_tac r2)
        apply(simp_all)
  apply(case_tac r2)
       apply(simp_all)
  done

lemma rsize0:
  shows "0 < rsize r"
  apply(induct  r)
       apply(auto)
  done


fun nonnested :: "rrexp \<Rightarrow> bool"
  where
  "nonnested (RALTS []) = True"
| "nonnested (RALTS ((RALTS rs1) # rs2)) = False"
| "nonnested (RALTS (r # rs2)) = nonnested (RALTS rs2)"
| "nonnested r = True"



lemma  k00:
  shows "rflts (rs1 @ rs2) = rflts rs1 @ rflts rs2"
  apply(induct rs1 arbitrary: rs2)
   apply(auto)
  by (metis append.assoc k0)




lemma k0b:
  assumes "nonalt r" "r \<noteq> RZERO"
  shows "rflts [r] = [r]"
  using assms
  apply(case_tac  r)
  apply(simp_all)
  done

lemma nn1:
  assumes "nonnested (RALTS rs)"
  shows "\<nexists> rs1. rflts rs = [RALTS rs1]"
  using assms
  apply(induct rs rule: rflts.induct)
  apply(auto)
  done

lemma nn1q:
  assumes "nonnested (RALTS rs)"
  shows "\<nexists>rs1. RALTS rs1 \<in> set (rflts rs)"
  using assms
  apply(induct rs rule: rflts.induct)
  apply(auto)
  done

lemma nn1qq:
  assumes "nonnested (RALTS rs)"
  shows "\<nexists> rs1. RALTS rs1 \<in> set rs"
  using assms
  apply(induct rs rule: rflts.induct)
  apply(auto)
  done

 

lemma n0:
  shows "nonnested (RALTS rs) \<longleftrightarrow> (\<forall>r \<in> set rs. nonalt r)"
  apply(induct rs )
   apply(auto)
    apply (metis list.set_intros(1) nn1qq nonalt.elims(3))
  apply (metis nonalt.elims(2) nonnested.simps(3) nonnested.simps(4) nonnested.simps(5) nonnested.simps(6) nonnested.simps(7))
  using bbbbs1 apply fastforce
  by (metis bbbbs1 list.set_intros(2) nn1qq)

  
  

lemma nn1c:
  assumes "\<forall>r \<in> set rs. nonnested r"
  shows "\<forall>r \<in> set (rflts rs). nonalt r"
  using assms
  apply(induct rs rule: rflts.induct)
        apply(auto)
  using n0 by blast

lemma nn1bb:
  assumes "\<forall>r \<in> set rs. nonalt r"
  shows "nonnested (rsimp_ALTs  rs)"
  using assms
  apply(induct  rs rule: rsimp_ALTs.induct)
    apply(auto)
  using nonalt.simps(1) nonnested.elims(3) apply blast
  using n0 by auto

lemma bsimp_ASEQ0:
  shows "rsimp_SEQ  r1 RZERO = RZERO"
  apply(induct r1)
  apply(auto)
  done

lemma nn1b:
  shows "nonnested (rsimp r)"
  apply(induct r)
       apply(simp_all)
  apply(case_tac "rsimp r1 = RZERO")
    apply(simp)
 apply(case_tac "rsimp r2 = RZERO")
   apply(simp)
    apply(subst bsimp_ASEQ0)
  apply(simp)
  apply(case_tac "\<exists>bs. rsimp r1 = RONE")
    apply(auto)[1]
  using idiot apply fastforce
  using idiot2 nonnested.simps(11) apply presburger
  by (metis (mono_tags, lifting) image_iff list.set_map nn1bb nn1c rdistinct_set_equality)

  
lemma nn1d:
  assumes "rsimp r = RALTS rs"
  shows "\<forall>r1 \<in> set rs. \<forall>  bs. r1 \<noteq> RALTS  rs2"
  using nn1b assms
  by (metis nn1qq)

lemma nn_flts:
  assumes "nonnested (RALTS rs)"
  shows "\<forall>r \<in>  set (rflts rs). nonalt r"
  using assms
  apply(induct rs rule: rflts.induct)
        apply(auto)
  done

lemma nonalt_flts_rd:
  shows "\<lbrakk>xa \<in> set (rdistinct (rflts (map rsimp rs)) {})\<rbrakk>
       \<Longrightarrow> nonalt xa"
  by (metis ex_map_conv nn1b nn1c rdistinct_set_equality)

lemma distinct_accLarge_empty:
  shows "rset \<subseteq> rset' \<Longrightarrow> rdistinct rs rset = [] \<Longrightarrow> rdistinct rs rset' = []"
  apply(induct rs arbitrary: rset rset')
   apply simp+
  by (metis list.distinct(1) subsetD)

lemma rsimpalts_implies1:
  shows " rsimp_ALTs (a # rdistinct rs {a}) = RZERO \<Longrightarrow> a = RZERO"
  using rsimp_ALTs.elims by auto


lemma rsimpalts_implies2:
  shows "rsimp_ALTs (a # rdistinct rs rset) = RZERO \<Longrightarrow> rdistinct rs rset = []"
  by (metis append_butlast_last_id rrexp.distinct(7) rsimpalts_conscons)

lemma rsimpalts_implies21:
  shows "rsimp_ALTs (a # rdistinct rs {a}) = RZERO \<Longrightarrow> rdistinct rs {a} = []"
  using rsimpalts_implies2 by blast


lemma hollow_removemore_hollow:
  shows "rsimp_ALTs (rdistinct rs {}) = RZERO \<Longrightarrow> 
rsimp_ALTs (rdistinct rs rset) = RZERO "
  apply(induct rs arbitrary: rset)
   apply simp
  apply simp
  apply(case_tac " a \<in> rset")
   apply simp
   apply(drule_tac x = "rset" in meta_spec)
  apply (smt (verit, best) Un_insert_left empty_iff rdistinct.elims rdistinct.simps(2) rrexp.distinct(7) rsimp_ALTs.simps(1) rsimp_ALTs.simps(3) singletonD sup_bot_left)
  apply simp
  apply(subgoal_tac "a = RZERO")
  apply(subgoal_tac "rdistinct rs (insert a rset) = []")
  using rsimp_ALTs.simps(2) apply presburger
   apply(subgoal_tac "rdistinct rs {a} = []")
  apply(subgoal_tac "{a} \<subseteq> insert a rset")
  apply (meson distinct_accLarge_empty)
    apply blast
  using rsimpalts_implies21 apply blast
  using rsimpalts_implies1 by blast

lemma bsimp_ASEQ2:
  shows "rsimp_SEQ RONE r2 =  r2"
  apply(induct r2)
  apply(auto)
  done

lemma elem_smaller_than_set:
  shows "xa \<in> set  list \<Longrightarrow> rsize xa < Suc ( sum_list (map rsize list))"
  apply(induct list)
   apply simp
  by (metis image_eqI le_imp_less_Suc list.set_map member_le_sum_list)


lemma smaller_corresponding:
  shows "xa \<in> set (map rsimp list) \<Longrightarrow> \<exists>xa' \<in> set list. rsize xa \<le> rsize xa'"
  apply(induct list)
   apply simp
  by (metis list.set_intros(1) list.set_intros(2) list.simps(9) rsimp_mono set_ConsD)

lemma simpelem_smaller_than_set:
  shows "xa \<in> set (map rsimp list) \<Longrightarrow> rsize xa < Suc ( sum_list (map rsize ( list)))"
  apply(subgoal_tac "\<exists>xa' \<in> set list. rsize xa \<le> rsize xa'")
   
  using elem_smaller_than_set order_le_less_trans apply blast
  using smaller_corresponding by presburger


lemma rsimp_list_mono:
  shows "sum_list (map rsize (map rsimp rs)) \<le> sum_list (map rsize rs)"
  apply(induct rs)
   apply simp+
  by (simp add: add_mono_thms_linordered_semiring(1) rsimp_mono)

lemma good1_obvious_but_isabelle_needs_clarification:
  shows "       \<lbrakk>\<forall>y. rsize y < Suc (rsize a + sum_list (map rsize list)) \<longrightarrow> good (rsimp y) \<or> rsimp y = RZERO;
        rsimp_ALTs (rdistinct (rflts (map rsimp list)) {}) = RZERO; good (rsimp a);
        xa \<in> set (rdistinct (rflts (rsimp a # map rsimp list)) {})\<rbrakk>
       \<Longrightarrow> rsize xa < Suc (rsize a + sum_list (map rsize list))"
  apply(subgoal_tac "rsize xa \<le> 
          sum_list (map rsize (rdistinct (rflts (rsimp a # map rsimp list)) {}))")
  apply(subgoal_tac "  sum_list (map rsize (rdistinct (rflts (rsimp a # map rsimp list)) {})) \<le>
                       sum_list (map rsize ( (rflts (rsimp a # map rsimp list))))")
  apply(subgoal_tac " sum_list (map rsize ( (rflts (rsimp a # map rsimp list)))) \<le>
                      sum_list (map rsize  (rsimp a # map rsimp list))")
  apply(subgoal_tac " sum_list (map rsize (rsimp a # map rsimp list)) \<le>
                      sum_list (map rsize (a # list))")
  apply simp
  apply (metis Cons_eq_map_conv rsimp_list_mono)
  using rflts_mono apply blast
  using rdistinct_phi_smaller apply blast
  using elem_smaller_than_set less_Suc_eq_le by blast

(*says anything coming out of simp+flts+db will be good*)
lemma good2_obv_simplified:
  shows " \<lbrakk>\<forall>y. rsize y < Suc (sum_list (map rsize rs)) \<longrightarrow> good (rsimp y) \<or> rsimp y = RZERO;
           xa \<in> set (rdistinct (rflts (map rsimp rs)) {}); good (rsimp xa) \<or> rsimp xa = RZERO\<rbrakk> \<Longrightarrow> good xa"
  apply(subgoal_tac " \<forall>xa' \<in> set (map rsimp rs). good xa' \<or> xa' = RZERO")
  prefer 2
  apply (simp add: elem_smaller_than_set)
  by (metis flts3 rdistinct_set_equality)

  


lemma good2_obvious_but_isabelle_needs_clarification:
  shows "\<And>a list xa.
       \<lbrakk>\<forall>y. rsize y < Suc (rsize a + sum_list (map rsize list)) \<longrightarrow> good (rsimp y) \<or> rsimp y = RZERO;
        rsimp_ALTs (rdistinct (rflts (map rsimp list)) {}) = RZERO; good (rsimp a);
        xa \<in> set (rdistinct (rflts (rsimp a # map rsimp list)) {}); good (rsimp xa) \<or> rsimp xa = RZERO\<rbrakk>
       \<Longrightarrow> good xa"
  by (metis good2_obv_simplified list.simps(9) sum_list.Cons)

  

lemma good1:
  shows "good (rsimp a) \<or> rsimp a = RZERO"
  apply(induct a taking: rsize rule: measure_induct)
  apply(case_tac x)
  apply(simp)
  apply(simp)
  apply(simp)
  prefer 3
    apply(simp)
   prefer 2
   apply(simp only:)
   apply simp
  apply (smt (verit, ccfv_threshold) add_mono_thms_linordered_semiring(1) elem_smaller_than_set good0 good2_obv_simplified le_eq_less_or_eq nonalt_flts_rd order_less_trans plus_1_eq_Suc rdistinct_does_the_job rdistinct_phi_smaller rflts_mono rsimp_ALTs.simps(1) rsimp_list_mono)
  apply simp
  apply(subgoal_tac "good (rsimp x41) \<or> rsimp x41 = RZERO")
   apply(subgoal_tac "good (rsimp x42) \<or> rsimp x42 = RZERO")
    apply(case_tac "rsimp x41 = RZERO")
     apply simp
    apply(case_tac "rsimp x42 = RZERO")
     apply simp
  using bsimp_ASEQ0 apply blast
    apply(subgoal_tac "good (rsimp x41)")
     apply(subgoal_tac "good (rsimp x42)")
      apply simp
  apply (metis bsimp_ASEQ2 good_SEQ idiot2)
  apply blast
  apply fastforce
  using less_add_Suc2 apply blast  
  using less_iff_Suc_add by blast



fun
  RL :: "rrexp \<Rightarrow> string set"
where
  "RL (RZERO) = {}"
| "RL (RONE) = {[]}"
| "RL (RCHAR c) = {[c]}"
| "RL (RSEQ r1 r2) = (RL r1) ;; (RL r2)"
| "RL (RALTS rs) = (\<Union> (set (map RL rs)))"
| "RL (RSTAR r) = (RL r)\<star>"


lemma RL_rnullable:
  shows "rnullable r = ([] \<in> RL r)"
  apply(induct r)
  apply(auto simp add: Sequ_def)
  done

lemma RL_rder:
  shows "RL (rder c r) = Der c (RL r)"
  apply(induct r)
  apply(auto simp add: Sequ_def Der_def)
        apply (metis append_Cons)
  using RL_rnullable apply blast
  apply (metis append_eq_Cons_conv)
  apply (metis append_Cons)
  apply (metis RL_rnullable append_eq_Cons_conv)
  apply (metis Star.step append_Cons)
  using Star_decomp by auto




lemma RL_rsimp_RSEQ:
  shows "RL (rsimp_SEQ r1 r2) = (RL r1 ;; RL r2)"
  apply(induct r1 r2 rule: rsimp_SEQ.induct)
  apply(simp_all)
  done

lemma RL_rsimp_RALTS:
  shows "RL (rsimp_ALTs rs) = (\<Union> (set (map RL rs)))"
  apply(induct rs rule: rsimp_ALTs.induct)
  apply(simp_all)
  done

lemma RL_rsimp_rdistinct:
  shows "(\<Union> (set (map RL (rdistinct rs {})))) = (\<Union> (set (map RL rs)))"
  apply(auto)
  apply (metis rdistinct_set_equality)
  by (metis rdistinct_set_equality)

lemma RL_rsimp_rflts:
  shows "(\<Union> (set (map RL (rflts rs)))) = (\<Union> (set (map RL rs)))"
  apply(induct rs rule: rflts.induct)
  apply(simp_all)
  done

lemma RL_rsimp:
  shows "RL r = RL (rsimp r)"
  apply(induct r rule: rsimp.induct)
       apply(auto simp add: Sequ_def RL_rsimp_RSEQ)
  using RL_rsimp_RALTS RL_rsimp_rdistinct RL_rsimp_rflts apply auto[1]
  by (smt (verit, del_insts) RL_rsimp_RALTS RL_rsimp_rdistinct RL_rsimp_rflts UN_E image_iff list.set_map)

lemma RL_rders:
  shows "RL (rders_simp r s) = RL (rders r s)"
  apply(induct s arbitrary: r rule: rev_induct)
   apply(simp)
  apply(simp add: rders_append rders_simp_append) 
  apply(subst RL_rsimp[symmetric])
  using RL_rder by force
  

lemma good1a:
  assumes "RL a \<noteq> {}"
  shows "good (rsimp a)"
  using good1 assms
  by (metis RL.simps(1) RL_rsimp)



lemma g1:
  assumes "good (rsimp_ALTs  rs)"
  shows "rsimp_ALTs  rs = RALTS rs \<or> (\<exists>r. rs = [r] \<and> rsimp_ALTs  [r] =  r)"
using assms
    apply(induct rs)
  apply(simp)
  apply(case_tac rs)
  apply(simp only:)
  apply(simp)
  apply(case_tac  list)
  apply(simp)
  by simp

lemma flts_0:
  assumes "nonnested (RALTS   rs)"
  shows "\<forall>r \<in> set (rflts rs). r \<noteq> RZERO"
  using assms
  apply(induct rs  rule: rflts.induct)
        apply(simp) 
       apply(simp) 
      defer
      apply(simp) 
     apply(simp) 
    apply(simp) 
apply(simp) 
  apply(rule ballI)
  apply(simp)
  done

lemma flts_0a:
  assumes "nonnested (RALTS   rs)"
  shows "RZERO \<notin> set (rflts rs)"
  using assms
  using flts_0 by blast 
  
lemma qqq1:
  shows "RZERO \<notin> set (rflts (map rsimp rs))"
  by (metis ex_map_conv flts3 good.simps(1) good1)


fun nonazero :: "rrexp \<Rightarrow> bool"
  where
  "nonazero RZERO = False"
| "nonazero r = True"

lemma flts_concat:
  shows "rflts rs = concat (map (\<lambda>r. rflts [r]) rs)"
  apply(induct rs)
   apply(auto)
  apply(subst k0)
  apply(simp)
  done

lemma flts_single1:
  assumes "nonalt r" "nonazero r"
  shows "rflts [r] = [r]"
  using assms
  apply(induct r)
  apply(auto)
  done

lemma flts_qq:
  assumes "\<forall>y. rsize y < Suc (sum_list (map rsize rs)) \<longrightarrow> good y \<longrightarrow> rsimp y = y" 
          "\<forall>r'\<in>set rs. good r' \<and> nonalt r'"
  shows "rflts (map rsimp rs) = rs"
  using assms
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(subst k0)
  apply(subgoal_tac "rflts [rsimp a] =  [a]")
   prefer 2
   apply(drule_tac x="a" in spec)
   apply(drule mp)
    apply(simp)
   apply(auto)[1]
  using good.simps(1) k0b apply blast
  apply(auto)[1]  
  done

lemma sublist_distinct:
  shows "distinct (rs1 @ rs2 ) \<Longrightarrow> distinct rs1 \<and> distinct rs2"
  using distinct_append by blast

lemma first2elem_distinct:
  shows "distinct (a # b # rs) \<Longrightarrow> a \<noteq> b"
  by force

lemma rdistinct_does_not_remove:
  shows "((\<forall>r \<in> rset. r \<notin> set rs) \<and> (distinct rs)) \<Longrightarrow> rdistinct rs rset = rs"
  by (metis append.right_neutral distinct_rdistinct_append rdistinct.simps(1))

lemma nonalt0_flts_keeps:
  shows "(a \<noteq> RZERO) \<and> (\<forall>rs. a \<noteq> RALTS rs) \<Longrightarrow> rflts (a # xs) = a # rflts xs"
  apply(case_tac a)
       apply simp+
  done


lemma nonalt0_fltseq:
  shows "\<forall>r \<in> set rs. r \<noteq> RZERO \<and> nonalt r \<Longrightarrow> rflts rs = rs"
  apply(induct rs)
   apply simp
  apply(case_tac "a = RZERO")
   apply fastforce
  apply(case_tac "\<exists>rs1. a = RALTS rs1")
   apply(erule exE)
   apply simp+
  using nonalt0_flts_keeps by presburger

  


lemma goodalts_nonalt:
  shows "good (RALTS rs) \<Longrightarrow> rflts rs = rs"
  apply(induct x == "RALTS rs" arbitrary: rs rule: good.induct)
    apply simp
  
  using good.simps(5) apply blast
  apply simp
  apply(case_tac "r1 = RZERO")
  using good.simps(1) apply force
  apply(case_tac "r2 = RZERO")
  using good.simps(1) apply force
  apply(subgoal_tac "rflts (r1 # r2 # rs) = r1 # r2 # rflts rs")
  prefer 2
   apply (metis nonalt.simps(1) rflts_def_idiot)
  apply(subgoal_tac "\<forall>r \<in> set rs. r \<noteq> RZERO \<and> nonalt r")
   apply(subgoal_tac "rflts rs = rs")
    apply presburger
  using nonalt0_fltseq apply presburger
  using good.simps(1) by blast
  

  


lemma test:
  assumes "good r"
  shows "rsimp r = r"

  using assms
  apply(induct rule: good.induct)
                      apply simp
                      apply simp
                      apply simp
                      apply simp
                      apply simp
                      apply(subgoal_tac "distinct (r1 # r2 # rs)")
  prefer 2
  using good.simps(6) apply blast
  apply(subgoal_tac "rflts (r1 # r2 # rs ) = r1 # r2 # rs")
  prefer 2
  using goodalts_nonalt apply blast

                      apply(subgoal_tac "r1 \<noteq> r2")
  prefer 2
                      apply (meson distinct_length_2_or_more)
                      apply(subgoal_tac "r1 \<notin> set rs")
                      apply(subgoal_tac "r2 \<notin> set rs")
                      apply(subgoal_tac "\<forall>r \<in> set rs. rsimp r = r")
                      apply(subgoal_tac "map rsimp rs = rs")
  apply simp             
                      apply(subgoal_tac "\<forall>r \<in>  {r1, r2}. r \<notin> set rs")
  apply (metis distinct_not_exist rdistinct_on_distinct)
  
                      apply blast
                      apply (meson map_idI)
                      apply (metis good.simps(6) insert_iff list.simps(15))

  apply (meson distinct.simps(2))
                      apply (simp add: distinct.simps(2) distinct_length_2_or_more)
                      apply simp+
  done



lemma rsimp_idem:
  shows "rsimp (rsimp r) = rsimp r"
  using test good1
  by force





corollary rsimp_inner_idem1:
  shows "rsimp r = RSEQ r1 r2 \<Longrightarrow> rsimp r1 = r1 \<and> rsimp r2 = r2"
  by (metis bsimp_ASEQ0 good.simps(7) good.simps(8) good1 good_SEQ rrexp.distinct(5) rsimp.simps(1) rsimp.simps(3) test)
  

corollary rsimp_inner_idem2:
  shows "rsimp r = RALTS rs \<Longrightarrow> \<forall>r' \<in> (set rs). rsimp r' = r'"
  by (metis flts2 good1 k0a rrexp.simps(12) test)
  

corollary rsimp_inner_idem3:
  shows "rsimp r = RALTS rs \<Longrightarrow> map rsimp rs = rs"
  by (meson map_idI rsimp_inner_idem2)

corollary rsimp_inner_idem4:
  shows "rsimp r = RALTS rs \<Longrightarrow> rflts rs = rs"
  by (metis good1 goodalts_nonalt rrexp.simps(12))


lemma head_one_more_simp:
  shows "map rsimp (r # rs) = map rsimp (( rsimp r) # rs)"
  by (simp add: rsimp_idem)

lemma head_one_more_dersimp:
  shows "map rsimp ((rder x (rders_simp r s) # rs)) = map rsimp ((rders_simp r (s@[x]) ) # rs)"
  using head_one_more_simp rders_simp_append rders_simp_one_char by presburger



lemma der_simp_nullability:
  shows "rnullable r = rnullable (rsimp r)"
  using RL_rnullable RL_rsimp by auto
  

lemma ders_simp_nullability:
  shows "rnullable (rders r s) = rnullable (rders_simp r s)"
  apply(induct s arbitrary: r rule: rev_induct)
   apply(simp)
  apply(simp add: rders_append rders_simp_append)
  apply(simp only: RL_rnullable)
  apply(simp only: RL_rder)
  apply(subst RL_rsimp[symmetric])
  apply(simp only: RL_rder)
  by (simp add: RL_rders)






lemma  first_elem_seqder:
  shows "\<not>rnullable r1p \<Longrightarrow> map rsimp (rder x (RSEQ r1p r2)
                   # rs) = map rsimp ((RSEQ (rder x r1p) r2) # rs) "
  by auto

lemma first_elem_seqder1:
  shows  "\<not>rnullable (rders_simp r xs) \<Longrightarrow> map rsimp ( (rder x (RSEQ (rders_simp r xs) r2)) # rs) = 
                                          map rsimp ( (RSEQ (rsimp (rder x (rders_simp r xs))) r2) # rs)"
  by (simp add: rsimp_idem)

lemma first_elem_seqdersimps:
  shows "\<not>rnullable (rders_simp r xs) \<Longrightarrow> map rsimp ( (rder x (RSEQ (rders_simp r xs) r2)) # rs) = 
                                          map rsimp ( (RSEQ (rders_simp r (xs @ [x])) r2) # rs)"
  using first_elem_seqder1 rders_simp_append by auto






lemma no_alt_short_list_after_simp:
  shows "RALTS rs = rsimp r \<Longrightarrow> rsimp_ALTs rs = RALTS rs"
  by (metis bbbbs good1 k0a rrexp.simps(12))


lemma no_further_dB_after_simp:
  shows "RALTS rs = rsimp r \<Longrightarrow> rdistinct rs {} = rs"
  apply(subgoal_tac "good (RALTS rs)")
  apply(subgoal_tac "distinct rs")
  using rdistinct_on_distinct apply blast
  apply (metis distinct.simps(1) distinct.simps(2) empty_iff good.simps(6) list.exhaust set_empty2)
  using good1 by fastforce


lemma idem_after_simp1:
  shows "rsimp_ALTs (rdistinct (rflts [rsimp aa]) {}) = rsimp aa"
  apply(case_tac "rsimp aa")
  apply simp+
  apply (metis no_alt_short_list_after_simp no_further_dB_after_simp)
  by simp

lemma identity_wwo0:
  shows "rsimp (rsimp_ALTs (RZERO # rs)) = rsimp (rsimp_ALTs rs)"
  by (metis idem_after_simp1 list.exhaust list.simps(8) list.simps(9) rflts.simps(2) rsimp.simps(2) rsimp.simps(3) rsimp_ALTs.simps(1) rsimp_ALTs.simps(2) rsimp_ALTs.simps(3))


lemma distinct_removes_last:
  shows "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct as rset = rdistinct (as @ [a]) rset"
and "rdistinct (ab # as @ [ab]) rset1 = rdistinct (ab # as) rset1"
  apply(induct as arbitrary: rset ab rset1 a)
     apply simp
    apply simp
  apply(case_tac "aa \<in> rset")
   apply(case_tac "a = aa")
  apply (metis append_Cons)
    apply simp
   apply(case_tac "a \<in> set as")
  apply (metis append_Cons rdistinct.simps(2) set_ConsD)
   apply(case_tac "a = aa")
    prefer 2
    apply simp
   apply (metis append_Cons)
  apply(case_tac "ab \<in> rset1")
  prefer 2
   apply(subgoal_tac "rdistinct (ab # (a # as) @ [ab]) rset1 = 
               ab # (rdistinct ((a # as) @ [ab]) (insert ab rset1))")
  prefer 2
  apply force
  apply(simp only:)
     apply(subgoal_tac "rdistinct (ab # a # as) rset1 = ab # (rdistinct (a # as) (insert ab rset1))")
    apply(simp only:)
    apply(subgoal_tac "rdistinct ((a # as) @ [ab]) (insert ab rset1) = rdistinct (a # as) (insert ab rset1)")
     apply blast
    apply(case_tac "a \<in> insert ab rset1")
     apply simp
     apply (metis insertI1)
    apply simp
    apply (meson insertI1)
   apply simp
  apply(subgoal_tac "rdistinct ((a # as) @ [ab]) rset1 = rdistinct (a # as) rset1")
   apply simp
  by (metis append_Cons insert_iff insert_is_Un rdistinct.simps(2))


lemma distinct_removes_middle:
  shows  "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct (as @ as2) rset = rdistinct (as @ [a] @ as2) rset"
and "rdistinct (ab # as @ [ab] @ as3) rset1 = rdistinct (ab # as @ as3) rset1"
   apply(induct as arbitrary: rset rset1 ab as2 as3 a)
     apply simp
    apply simp
   apply(case_tac "a \<in> rset")
    apply simp
    apply metis
   apply simp
   apply (metis insertI1)
  apply(case_tac "a = ab")
   apply simp
   apply(case_tac "ab \<in> rset")
    apply simp
    apply presburger
   apply (meson insertI1)
  apply(case_tac "a \<in> rset")
  apply (metis (no_types, opaque_lifting) Un_insert_left append_Cons insert_iff rdistinct.simps(2) sup_bot_left)
  apply(case_tac "ab \<in> rset")
  apply simp
   apply (meson insert_iff)
  apply simp
  by (metis insertI1)


lemma distinct_removes_middle3:
  shows  "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct (as @ a #as2) rset = rdistinct (as @ as2) rset"
  using distinct_removes_middle(1) by fastforce

lemma distinct_removes_last2:
  shows "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct as rset = rdistinct (as @ [a]) rset"
  by (simp add: distinct_removes_last(1))

lemma distinct_removes_middle2:
  shows "a \<in> set as \<Longrightarrow> rdistinct (as @ [a] @ rs) {} = rdistinct (as @ rs) {}"
  by (metis distinct_removes_middle(1))

lemma distinct_removes_list:
  shows "\<lbrakk> \<forall>r \<in> set rs. r \<in> set as\<rbrakk> \<Longrightarrow> rdistinct (as @ rs) {} = rdistinct as {}"
  apply(induct rs)
   apply simp+
  apply(subgoal_tac "rdistinct (as @ a # rs) {} = rdistinct (as @ rs) {}")
   prefer 2
  apply (metis append_Cons append_Nil distinct_removes_middle(1))
  by presburger


lemma spawn_simp_rsimpalts:
  shows "rsimp (rsimp_ALTs rs) = rsimp (rsimp_ALTs (map rsimp rs))"
  apply(cases rs)
   apply simp
  apply(case_tac list)
   apply simp
   apply(subst rsimp_idem[symmetric])
   apply simp
  apply(subgoal_tac "rsimp_ALTs rs = RALTS rs")
   apply(simp only:)
   apply(subgoal_tac "rsimp_ALTs (map rsimp rs) = RALTS (map rsimp rs)")
    apply(simp only:)
  prefer 2
  apply simp
   prefer 2
  using rsimp_ALTs.simps(3) apply presburger
  apply auto
  apply(subst rsimp_idem)+
  by (metis comp_apply rsimp_idem)






lemma rsimp_no_dup:
  shows "rsimp r = RALTS rs \<Longrightarrow> distinct rs"
  by (metis no_further_dB_after_simp rdistinct_does_the_job)




lemma simp_singlealt_flatten:
  shows "rsimp (RALTS [RALTS rsa]) = rsimp (RALTS (rsa @ []))"
  apply(induct rsa)
   apply simp
  apply simp
  by (metis idem_after_simp1 list.simps(9) rsimp.simps(2))


lemma good1_rsimpalts:
  shows "rsimp r = RALTS rs \<Longrightarrow> rsimp_ALTs rs = RALTS rs"
  by (metis no_alt_short_list_after_simp) 
  



lemma good1_flatten:
  shows "\<lbrakk> rsimp r =  (RALTS rs1)\<rbrakk>
       \<Longrightarrow> rflts (rsimp_ALTs rs1 # map rsimp rsb) = rflts (rs1 @ map rsimp rsb)"
  apply(subst good1_rsimpalts)
   apply simp+
  apply(subgoal_tac "rflts (rs1 @ map rsimp rsb) = rs1 @ rflts (map rsimp rsb)")
   apply simp
  using flts_append rsimp_inner_idem4 by presburger

  
lemma flatten_rsimpalts:
  shows "rflts (rsimp_ALTs (rdistinct (rflts (map rsimp rsa)) {}) # map rsimp rsb) = 
         rflts ( (rdistinct (rflts (map rsimp rsa)) {}) @ map rsimp rsb)"
  apply(case_tac "map rsimp rsa")
   apply simp
  apply(case_tac "list")
   apply simp
   apply(case_tac a)
        apply simp+
    apply(rename_tac rs1)
    apply (metis good1_flatten map_eq_Cons_D no_further_dB_after_simp)
  
  apply simp
  
  apply(subgoal_tac "\<forall>r \<in> set( rflts (map rsimp rsa)). good r")
   apply(case_tac "rdistinct (rflts (map rsimp rsa)) {}")
    apply simp
   apply(case_tac "listb")
    apply simp+
  apply (metis Cons_eq_appendI good1_flatten rflts.simps(3) rsimp.simps(2) rsimp_ALTs.simps(3))
  by (metis (mono_tags, lifting) flts3 good1 image_iff list.set_map)


lemma last_elem_out:
  shows "\<lbrakk>x \<notin> set xs; x \<notin> rset \<rbrakk> \<Longrightarrow> rdistinct (xs @ [x]) rset = rdistinct xs rset @ [x]"
  apply(induct xs arbitrary: rset)
  apply simp+
  done




lemma rdistinct_concat_general:
  shows "rdistinct (rs1 @ rs2) {} = (rdistinct rs1 {}) @ (rdistinct rs2 (set rs1))"
  apply(induct rs1 arbitrary: rs2 rule: rev_induct)
   apply simp
  apply(drule_tac x = "x # rs2" in meta_spec)
  apply simp
  apply(case_tac "x \<in> set xs")
   apply simp
  
   apply (simp add: distinct_removes_middle3 insert_absorb)
  apply simp
  by (simp add: last_elem_out)


  

lemma distinct_once_enough:
  shows "rdistinct (rs @ rsa) {} = rdistinct (rdistinct rs {} @ rsa) {}"
  apply(subgoal_tac "distinct (rdistinct rs {})")
   apply(subgoal_tac 
" rdistinct (rdistinct rs {} @ rsa) {} = rdistinct rs {} @ (rdistinct rsa (set rs))")
  apply(simp only:)
  using rdistinct_concat_general apply blast
  apply (simp add: distinct_rdistinct_append rdistinct_set_equality)
  by (simp add: rdistinct_does_the_job)
  

lemma simp_flatten:
  shows "rsimp (RALTS ((RALTS rsa) # rsb)) = rsimp (RALTS (rsa @ rsb))"
  apply simp
  apply(subst flatten_rsimpalts)
  apply(simp add: flts_append)
  by (metis distinct_once_enough nonalt0_fltseq nonalt_flts_rd qqq1 rdistinct_set_equality)

lemma basic_rsimp_SEQ_property1:
  shows "rsimp_SEQ RONE r = r"
  by (simp add: idiot)



lemma basic_rsimp_SEQ_property3:
  shows "rsimp_SEQ r RZERO = RZERO"  
  using rsimp_SEQ.elims by blast



fun vsuf :: "char list \<Rightarrow> rrexp \<Rightarrow> char list list" where
"vsuf [] _ = []"
|"vsuf (c#cs) r1 = (if (rnullable r1) then  (vsuf cs (rder c r1)) @ [c # cs]
                                      else  (vsuf cs (rder c r1))
                   ) "






fun star_update :: "char \<Rightarrow> rrexp \<Rightarrow> char list list \<Rightarrow> char list list" where
"star_update c r [] = []"
|"star_update c r (s # Ss) = (if (rnullable (rders r s)) 
                                then (s@[c]) # [c] # (star_update c r Ss) 
                               else   (s@[c]) # (star_update c r Ss) )"


fun star_updates :: "char list \<Rightarrow> rrexp \<Rightarrow> char list list \<Rightarrow> char list list"
  where
"star_updates [] r Ss = Ss"
| "star_updates (c # cs) r Ss = star_updates cs r (star_update c r Ss)"

lemma stupdates_append: shows 
"star_updates (s @ [c]) r Ss = star_update c r (star_updates s r Ss)"
  apply(induct s arbitrary: Ss)
   apply simp
  apply simp
  done


lemma distinct_flts_no0:
  shows "  rflts (map rsimp (rdistinct rs (insert RZERO rset)))  =
           rflts (map rsimp (rdistinct rs rset))  "
  
  apply(induct rs arbitrary: rset)
   apply simp
  apply(case_tac a)
  apply simp+
    apply (smt (verit, ccfv_SIG) rflts.simps(2) rflts.simps(3) rflts_def_idiot)
  prefer 2
  apply simp  
  by (smt (verit, ccfv_threshold) Un_insert_right insert_iff list.simps(9) rdistinct.simps(2) rflts.simps(2) rflts.simps(3) rflts_def_idiot rrexp.distinct(7))

lemma flts_removes0:
  shows "  rflts (rs @ [RZERO])  =
           rflts rs"
  apply(induct rs)
   apply simp
  by (metis append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)
  

lemma rflts_spills_last:
  shows "a = RALTS rs \<Longrightarrow> rflts (rs1 @ [a]) = rflts rs1 @ rs"
  apply (induct rs1)
  apply simp
  by (metis append.assoc append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)

lemma flts_keeps1:
  shows " rflts (rs @ [RONE]) = 
          rflts  rs @ [RONE] "
  apply (induct rs)
   apply simp
  by (metis append.assoc append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)

lemma flts_keeps_others:
  shows "\<lbrakk>a \<noteq> RZERO; \<nexists>rs1. a = RALTS rs1\<rbrakk> \<Longrightarrow>rflts (rs @ [a]) = rflts rs @ [a]"
  apply(induct rs)
   apply simp
  apply (simp add: rflts_def_idiot)
  apply(case_tac a)
       apply simp
  using flts_keeps1 apply blast
     apply (metis append.assoc append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)
  apply (metis append.assoc append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)
  apply blast
  by (metis append.assoc append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)

lemma spilled_alts_contained:
  shows "\<lbrakk>a = RALTS rs ; a \<in> set rs1\<rbrakk> \<Longrightarrow> \<forall>r \<in> set rs. r \<in> set (rflts rs1)"
  apply(induct rs1)
   apply simp 
  apply(case_tac "a = aa")
   apply simp
  apply(subgoal_tac " a \<in> set rs1")
  prefer 2
   apply (meson set_ConsD)
  apply(case_tac aa)
  using rflts.simps(2) apply presburger
      apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  by fastforce


lemma distinct_removes_duplicate_flts:
  shows " a \<in> set rsa
       \<Longrightarrow> rdistinct (rflts (map rsimp rsa @ [rsimp a])) {} =
           rdistinct (rflts (map rsimp rsa)) {}"
  apply(subgoal_tac "rsimp a \<in> set (map rsimp rsa)")
  prefer 2
  apply simp
  apply(induct "rsimp a")
       apply simp
  using flts_removes0 apply presburger
      apply(subgoal_tac " rdistinct (rflts (map rsimp rsa @ [rsimp a])) {} =  
                          rdistinct (rflts (map rsimp rsa @ [RONE])) {}")
      apply (simp only:)
       apply(subst flts_keeps1)
  apply (metis distinct_removes_last2 rflts_def_idiot2 rrexp.simps(20) rrexp.simps(6))
      apply presburger
        apply(subgoal_tac " rdistinct (rflts (map rsimp rsa @ [rsimp a]))    {} =  
                            rdistinct ((rflts (map rsimp rsa)) @ [RCHAR x]) {}")
      apply (simp only:)
      prefer 2
      apply (metis flts_keeps_others rrexp.distinct(21) rrexp.distinct(3))
  apply (metis distinct_removes_last2 rflts_def_idiot2 rrexp.distinct(21) rrexp.distinct(3))

    apply (metis distinct_removes_last2 flts_keeps_others rflts_def_idiot2 rrexp.distinct(25) rrexp.distinct(5))
   prefer 2
   apply (metis distinct_removes_last2 flts_keeps_others flts_removes0 rflts_def_idiot2 rrexp.distinct(29))
  apply(subgoal_tac "rflts (map rsimp rsa @ [rsimp a]) = rflts (map rsimp rsa) @ x")
  prefer 2
  apply (simp add: rflts_spills_last)
  apply(simp only:)
  apply(subgoal_tac "\<forall> r \<in> set x. r \<in> set (rflts (map rsimp rsa))")
  prefer 2
  using spilled_alts_contained apply presburger
  using distinct_removes_list by blast



(*some basic facts about rsimp*)




end
theory BlexerSimp2
  imports Blexer ClosedFormsBounds
begin

fun rerase :: "arexp \<Rightarrow> rrexp"
where
  "rerase AZERO = RZERO"
| "rerase (AONE _) = RONE"
| "rerase (ACHAR _ c) = RCHAR c"
| "rerase (AALTs bs rs) = RALTS (map rerase rs)"
| "rerase (ASEQ _ r1 r2) = RSEQ (rerase r1) (rerase r2)"
| "rerase (ASTAR _ r) = RSTAR (rerase r)"

lemma rerase_fuse:
  shows "rerase (fuse bs r) = rerase r"
  apply(induct r)
       apply simp+
  done



fun distinctBy :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a list"
  where
  "distinctBy [] f acc = []"
| "distinctBy (x#xs) f acc = 
     (if (f x) \<in> acc then distinctBy xs f acc 
      else x # (distinctBy xs f ({f x} \<union> acc)))"

 

fun flts :: "arexp list \<Rightarrow> arexp list"
  where 
  "flts [] = []"
| "flts (AZERO # rs) = flts rs"
| "flts ((AALTs bs  rs1) # rs) = (map (fuse bs) rs1) @ flts rs"
| "flts (r1 # rs) = r1 # flts rs"



fun bsimp_ASEQ :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp"
  where
  "bsimp_ASEQ _ AZERO _ = AZERO"
| "bsimp_ASEQ _ _ AZERO = AZERO"
| "bsimp_ASEQ bs1 (AONE bs2) r2 = fuse (bs1 @ bs2) r2"
| "bsimp_ASEQ bs1 r1 r2 = ASEQ  bs1 r1 r2"

lemma bsimp_ASEQ0[simp]:
  shows "bsimp_ASEQ bs r1 AZERO = AZERO"
  by (case_tac r1)(simp_all)

lemma bsimp_ASEQ1:
  assumes "r1 \<noteq> AZERO" "r2 \<noteq> AZERO" "\<nexists>bs. r1 = AONE bs"
  shows "bsimp_ASEQ bs r1 r2 = ASEQ bs r1 r2"
  using assms
  apply(induct bs r1 r2 rule: bsimp_ASEQ.induct)
  apply(auto)
  done

lemma bsimp_ASEQ2[simp]:
  shows "bsimp_ASEQ bs1 (AONE bs2) r2 = fuse (bs1 @ bs2) r2"
  by (case_tac r2) (simp_all)


fun bsimp_AALTs :: "bit list \<Rightarrow> arexp list \<Rightarrow> arexp"
  where
  "bsimp_AALTs _ [] = AZERO"
| "bsimp_AALTs bs1 [r] = fuse bs1 r"
| "bsimp_AALTs bs1 rs = AALTs bs1 rs"




fun bsimp :: "arexp \<Rightarrow> arexp" 
  where
  "bsimp (ASEQ bs1 r1 r2) = bsimp_ASEQ bs1 (bsimp r1) (bsimp r2)"
| "bsimp (AALTs bs1 rs) = bsimp_AALTs bs1 (distinctBy (flts (map bsimp rs)) rerase {}) "
| "bsimp r = r"


fun 
  bders_simp :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders_simp r [] = r"
| "bders_simp r (c # s) = bders_simp (bsimp (bder c r)) s"

definition blexer_simp where
 "blexer_simp r s \<equiv> if bnullable (bders_simp (intern r) s) then 
                    decode (bmkeps (bders_simp (intern r) s)) r else None"



lemma bders_simp_append:
  shows "bders_simp r (s1 @ s2) = bders_simp (bders_simp r s1) s2"
  apply(induct s1 arbitrary: r s2)
  apply(simp_all)
  done

lemma RL_bsimp_ASEQ:
  "RL (rerase (ASEQ bs r1 r2)) = RL (rerase (bsimp_ASEQ bs r1 r2))"
  apply(induct bs r1 r2 rule: bsimp_ASEQ.induct)
  apply simp+
  done

lemma RL_bsimp_AALTs:
 "RL (rerase (AALTs bs rs)) = RL (rerase (bsimp_AALTs bs rs))"
  apply(induct bs rs rule: bsimp_AALTs.induct)
  apply(simp_all add: rerase_fuse)
  done


lemma RL_erase_flts:
  shows "\<Union> (RL ` rerase ` (set (flts rs))) =
         \<Union> (RL ` rerase ` (set rs))"
  apply(induct rs rule: flts.induct)
        apply simp+
      apply auto
  apply (smt (verit) fuse.elims rerase.simps(2) rerase.simps(3) rerase.simps(4) rerase.simps(5) rerase.simps(6))
  by (smt (verit, best) fuse.elims rerase.simps(2) rerase.simps(3) rerase.simps(4) rerase.simps(5) rerase.simps(6))


lemma RL_rerase_dB_acc:
  shows "(\<Union> (RL ` acc) \<union> (\<Union> (RL ` rerase ` (set (distinctBy rs rerase acc)))))
           = \<Union> (RL ` acc) \<union> \<Union> (RL ` rerase ` (set rs))"
  apply(induction rs arbitrary: acc)
   apply simp_all
    by (smt (z3) SUP_absorb UN_insert sup_assoc sup_commute)

lemma RL_rerase_dB:
  shows "(\<Union> (RL ` rerase ` (set (distinctBy rs rerase {})))) = \<Union> (RL ` rerase ` (set rs))"
  by (metis RL_rerase_dB_acc Un_commute Union_image_empty)


lemma RL_bsimp_rerase:
  shows "RL (rerase r) = RL (rerase (bsimp r))"
  apply(induct r)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(auto simp add: Sequ_def)[1]
  apply(subst RL_bsimp_ASEQ[symmetric])
  apply(auto simp add: Sequ_def)[1]
  apply(subst (asm)  RL_bsimp_ASEQ[symmetric])
  apply(auto simp add: Sequ_def)[1]
  apply(simp)
  apply(subst RL_bsimp_AALTs[symmetric])
  defer
  apply(simp)
  using RL_erase_flts RL_rerase_dB by force

lemma rder_correctness:
  shows "RL (rder c r) = Der c (RL r)"
  by (simp add: RL_rder)




lemma asize_rsize:
  shows "rsize (rerase r) = asize r"
  apply(induct r)
       apply simp+
  
  apply (metis (mono_tags, lifting) comp_apply map_eq_conv)
  by simp

lemma rb_nullability:
  shows " rnullable (rerase a) = bnullable a"
  apply(induct a)
       apply simp+
  done

lemma rder_bder_rerase:
  shows "rder c (rerase r ) = rerase (bder c r)"
  apply (induct r)
       apply simp+
    apply(case_tac "bnullable r1")
     apply simp
  apply (simp add: rb_nullability rerase_fuse)
  using rb_nullability apply presburger
   apply simp
  apply simp
  done



lemma RL_bder_preserved:
  shows "RL (rerase a1) = RL (rerase a2) \<Longrightarrow> RL (rerase (bder c a1 )) = RL (rerase (bder c a2))"
  by (metis rder_bder_rerase rder_correctness)


lemma RL_bders_simp:
  shows "RL (rerase (bders_simp r s)) = RL (rerase (bders r s))"
  apply(induct s arbitrary: r rule: rev_induct)
  apply(simp)
  apply(simp add: bders_append)
  apply(simp add: bders_simp_append)
  apply(simp add: RL_bsimp_rerase[symmetric])
  using RL_bder_preserved by blast



lemma bmkeps_fuse:
  assumes "bnullable r"
  shows "bmkeps (fuse bs r) = bs @ bmkeps r"
  by (metis assms bmkeps_retrieve bnullable_correctness erase_fuse mkeps_nullable retrieve_fuse2)

lemma bmkepss_fuse: 
  assumes "bnullables rs"
  shows "bmkepss (map (fuse bs) rs) = bs @ bmkepss rs"
  using assms
  apply(induct rs arbitrary: bs)
  apply(auto simp add: bmkeps_fuse bnullable_fuse)
  done


lemma b4:
  shows "bnullable (bders_simp r s) = bnullable (bders r s)"
proof -
  have "RL (rerase (bders_simp r s)) = RL (rerase (bders r s))"
    by (simp add: RL_bders_simp)
  then show "bnullable (bders_simp r s) = bnullable (bders r s)"
    using RL_rnullable rb_nullability by blast
qed


lemma bder_fuse:
  shows "bder c (fuse bs a) = fuse bs  (bder c a)"
  apply(induct a arbitrary: bs c)
       apply(simp_all)
  done




inductive 
  rrewrite:: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ \<leadsto> _" [99, 99] 99)
and 
  srewrite:: "arexp list \<Rightarrow> arexp list \<Rightarrow> bool" (" _ s\<leadsto> _" [100, 100] 100)
where
  bs1: "ASEQ bs AZERO r2 \<leadsto> AZERO"
| bs2: "ASEQ bs r1 AZERO \<leadsto> AZERO"
| bs3: "ASEQ bs1 (AONE bs2) r \<leadsto> fuse (bs1@bs2) r"
| bs4: "r1 \<leadsto> r2 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r2 r3"
| bs5: "r3 \<leadsto> r4 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r1 r4"
| bs6: "AALTs bs [] \<leadsto> AZERO"
| bs7: "AALTs bs [r] \<leadsto> fuse bs r"
| bs10: "rs1 s\<leadsto> rs2 \<Longrightarrow> AALTs bs rs1 \<leadsto> AALTs bs rs2"
| ss1:  "[] s\<leadsto> []"
| ss2:  "rs1 s\<leadsto> rs2 \<Longrightarrow> (r # rs1) s\<leadsto> (r # rs2)"
| ss3:  "r1 \<leadsto> r2 \<Longrightarrow> (r1 # rs) s\<leadsto> (r2 # rs)"
| ss4:  "(AZERO # rs) s\<leadsto> rs"
| ss5:  "(AALTs bs1 rs1 # rsb) s\<leadsto> ((map (fuse bs1) rs1) @ rsb)"
| ss6:  "rerase a1 = rerase a2 \<Longrightarrow> (rsa@[a1]@rsb@[a2]@rsc) s\<leadsto> (rsa@[a1]@rsb@rsc)"


inductive 
  rrewrites:: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ \<leadsto>* _" [100, 100] 100)
where 
  rs1[intro, simp]:"r \<leadsto>* r"
| rs2[intro]: "\<lbrakk>r1 \<leadsto>* r2; r2 \<leadsto> r3\<rbrakk> \<Longrightarrow> r1 \<leadsto>* r3"

inductive 
  srewrites:: "arexp list \<Rightarrow> arexp list \<Rightarrow> bool" ("_ s\<leadsto>* _" [100, 100] 100)
where 
  sss1[intro, simp]:"rs s\<leadsto>* rs"
| sss2[intro]: "\<lbrakk>rs1 s\<leadsto> rs2; rs2 s\<leadsto>* rs3\<rbrakk> \<Longrightarrow> rs1 s\<leadsto>* rs3"


lemma r_in_rstar : "r1 \<leadsto> r2 \<Longrightarrow> r1 \<leadsto>* r2"
  using rrewrites.intros(1) rrewrites.intros(2) by blast
 
lemma rrewrites_trans[trans]: 
  assumes a1: "r1 \<leadsto>* r2"  and a2: "r2 \<leadsto>* r3"
  shows "r1 \<leadsto>* r3"
  using a2 a1
  apply(induct r2 r3 arbitrary: r1 rule: rrewrites.induct) 
  apply(auto)
  done

lemma srewrites_trans[trans]: 
  assumes a1: "r1 s\<leadsto>* r2"  and a2: "r2 s\<leadsto>* r3"
  shows "r1 s\<leadsto>* r3"
  using a1 a2
  apply(induct r1 r2 arbitrary: r3 rule: srewrites.induct) 
   apply(auto)
  done



lemma contextrewrites0: 
  "rs1 s\<leadsto>* rs2 \<Longrightarrow> AALTs bs rs1 \<leadsto>* AALTs bs rs2"
  apply(induct rs1 rs2 rule: srewrites.inducts)
   apply simp
  using bs10 r_in_rstar rrewrites_trans by blast

lemma contextrewrites1: 
  "r \<leadsto>* r' \<Longrightarrow> AALTs bs (r # rs) \<leadsto>* AALTs bs (r' # rs)"
  apply(induct r r' rule: rrewrites.induct)
   apply simp
  using bs10 ss3 by blast

lemma srewrite1: 
  shows "rs1 s\<leadsto> rs2 \<Longrightarrow> (rs @ rs1) s\<leadsto> (rs @ rs2)"
  apply(induct rs)
   apply(auto)
  using ss2 by auto

lemma srewrites1: 
  shows "rs1 s\<leadsto>* rs2 \<Longrightarrow> (rs @ rs1) s\<leadsto>* (rs @ rs2)"
  apply(induct rs1 rs2 rule: srewrites.induct)
   apply(auto)
  using srewrite1 by blast

lemma srewrite2: 
  shows  "r1 \<leadsto> r2 \<Longrightarrow> True"
  and "rs1 s\<leadsto> rs2 \<Longrightarrow> (rs1 @ rs) s\<leadsto>* (rs2 @ rs)"
  apply(induct rule: rrewrite_srewrite.inducts)
               apply(auto)
     apply (metis append_Cons append_Nil srewrites1)
    apply(meson srewrites.simps ss3)
  apply (meson srewrites.simps ss4)
  apply (meson srewrites.simps ss5)
  by (metis append_Cons append_Nil srewrites.simps ss6)
  

lemma srewrites3: 
  shows "rs1 s\<leadsto>* rs2 \<Longrightarrow> (rs1 @ rs) s\<leadsto>* (rs2 @ rs)"
  apply(induct rs1 rs2 arbitrary: rs rule: srewrites.induct)
   apply(auto)
  by (meson srewrite2(2) srewrites_trans)

(*
lemma srewrites4:
  assumes "rs3 s\<leadsto>* rs4" "rs1 s\<leadsto>* rs2" 
  shows "(rs1 @ rs3) s\<leadsto>* (rs2 @ rs4)"
  using assms
  apply(induct rs3 rs4 arbitrary: rs1 rs2 rule: srewrites.induct)
  apply (simp add: srewrites3)
  using srewrite1 by blast
*)

lemma srewrites6:
  assumes "r1 \<leadsto>* r2" 
  shows "[r1] s\<leadsto>* [r2]"
  using assms
  apply(induct r1 r2 rule: rrewrites.induct)
   apply(auto)
  by (meson srewrites.simps srewrites_trans ss3)

lemma srewrites7:
  assumes "rs3 s\<leadsto>* rs4" "r1 \<leadsto>* r2" 
  shows "(r1 # rs3) s\<leadsto>* (r2 # rs4)"
  using assms
  by (smt (verit, best) append_Cons append_Nil srewrites1 srewrites3 srewrites6 srewrites_trans)

lemma ss6_stronger_aux:
  shows "(rs1 @ rs2) s\<leadsto>* (rs1 @ distinctBy rs2 rerase (set (map rerase rs1)))"
  apply(induct rs2 arbitrary: rs1)
   apply(auto)
  apply (smt (verit, best) append.assoc append.right_neutral append_Cons append_Nil split_list srewrite2(2) srewrites_trans ss6)
  apply(drule_tac x="rs1 @ [a]" in meta_spec)
  apply(simp)
  done

lemma ss6_stronger:
  shows "rs1 s\<leadsto>* distinctBy rs1 rerase {}"
  by (metis append_Nil list.set(1) list.simps(8) ss6_stronger_aux)


lemma rewrite_preserves_fuse: 
  shows "r2 \<leadsto> r3 \<Longrightarrow> fuse bs r2 \<leadsto> fuse bs r3"
  and   "rs2 s\<leadsto> rs3 \<Longrightarrow> map (fuse bs) rs2 s\<leadsto>* map (fuse bs) rs3"
proof(induct rule: rrewrite_srewrite.inducts)
  case (bs3 bs1 bs2 r)
  then show ?case
    by (metis fuse.simps(5) fuse_append rrewrite_srewrite.bs3) 
next
  case (bs7 bs r)
  then show ?case
    by (metis fuse.simps(4) fuse_append rrewrite_srewrite.bs7) 
next
  case (ss2 rs1 rs2 r)
  then show ?case
    using srewrites7 by force 
next
  case (ss3 r1 r2 rs)
  then show ?case by (simp add: r_in_rstar srewrites7)
next
  case (ss5 bs1 rs1 rsb)
  then show ?case 
    apply(simp)
    by (metis (mono_tags, lifting) comp_def fuse_append map_eq_conv rrewrite_srewrite.ss5 srewrites.simps)
next
  case (ss6 a1 a2 rsa rsb rsc)
  then show ?case 
    apply(simp only: map_append)
    by (smt (verit, ccfv_threshold) rerase_fuse list.simps(8) list.simps(9) rrewrite_srewrite.ss6 srewrites.simps)  
qed (auto intro: rrewrite_srewrite.intros)


lemma rewrites_fuse:  
  assumes "r1 \<leadsto>* r2"
  shows "fuse bs r1 \<leadsto>* fuse bs r2"
using assms
apply(induction r1 r2 arbitrary: bs rule: rrewrites.induct)
apply(auto intro: rewrite_preserves_fuse rrewrites_trans)
done


lemma star_seq:  
  assumes "r1 \<leadsto>* r2"
  shows "ASEQ bs r1 r3 \<leadsto>* ASEQ bs r2 r3"
using assms
apply(induct r1 r2 arbitrary: r3 rule: rrewrites.induct)
apply(auto intro: rrewrite_srewrite.intros)
done

lemma star_seq2:  
  assumes "r3 \<leadsto>* r4"
  shows "ASEQ bs r1 r3 \<leadsto>* ASEQ bs r1 r4"
  using assms
apply(induct r3 r4 arbitrary: r1 rule: rrewrites.induct)
apply(auto intro: rrewrite_srewrite.intros)
done

lemma continuous_rewrite: 
  assumes "r1 \<leadsto>* AZERO"
  shows "ASEQ bs1 r1 r2 \<leadsto>* AZERO"
using assms bs1 star_seq by blast

(*
lemma continuous_rewrite2: 
  assumes "r1 \<leadsto>* AONE bs"
  shows "ASEQ bs1 r1 r2 \<leadsto>* (fuse (bs1 @ bs) r2)"
  using assms  by (meson bs3 rrewrites.simps star_seq)
*)

lemma bsimp_aalts_simpcases: 
  shows "AONE bs \<leadsto>* bsimp (AONE bs)"  
  and   "AZERO \<leadsto>* bsimp AZERO" 
  and   "ACHAR bs c \<leadsto>* bsimp (ACHAR bs c)"
  by (simp_all)

lemma bsimp_AALTs_rewrites: 
  shows "AALTs bs1 rs \<leadsto>* bsimp_AALTs bs1 rs"
  by (smt (verit) bs6 bs7 bsimp_AALTs.elims rrewrites.simps)

lemma trivialbsimp_srewrites: 
  "\<lbrakk>\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* f x \<rbrakk> \<Longrightarrow> rs s\<leadsto>* (map f rs)"
  apply(induction rs)
   apply simp
  apply(simp)
  using srewrites7 by auto



lemma fltsfrewrites: "rs s\<leadsto>* flts rs"
  apply(induction rs rule: flts.induct)
  apply(auto intro: rrewrite_srewrite.intros)
  apply (meson srewrites.simps srewrites1 ss5)
  using rs1 srewrites7 apply presburger
  using srewrites7 apply force
  apply (simp add: srewrites7)
  by (simp add: srewrites7)

lemma bnullable0:
shows "r1 \<leadsto> r2 \<Longrightarrow> bnullable r1 = bnullable r2" 
  and "rs1 s\<leadsto> rs2 \<Longrightarrow> bnullables rs1 = bnullables rs2" 
  apply(induct rule: rrewrite_srewrite.inducts)
  apply(auto simp add:  bnullable_fuse)
   apply (meson UnCI bnullable_fuse imageI)
  by (metis rb_nullability)


lemma rewritesnullable: 
  assumes "r1 \<leadsto>* r2" 
  shows "bnullable r1 = bnullable r2"
using assms 
  apply(induction r1 r2 rule: rrewrites.induct)
  apply simp
  using bnullable0(1) by auto

lemma rewrite_bmkeps_aux: 
  shows "r1 \<leadsto> r2 \<Longrightarrow> (bnullable r1 \<and> bnullable r2 \<Longrightarrow> bmkeps r1 = bmkeps r2)"
  and   "rs1 s\<leadsto> rs2 \<Longrightarrow> (bnullables rs1 \<and> bnullables rs2 \<Longrightarrow> bmkepss rs1 = bmkepss rs2)" 
proof (induct rule: rrewrite_srewrite.inducts)
  case (bs3 bs1 bs2 r)
  then show ?case by (simp add: bmkeps_fuse) 
next
  case (bs7 bs r)
  then show ?case by (simp add: bmkeps_fuse) 
next
  case (ss3 r1 r2 rs)
  then show ?case
    using bmkepss.simps bnullable0(1) by presburger
next
  case (ss5 bs1 rs1 rsb)
  then show ?case
    by (simp add: bmkepss1 bmkepss2 bmkepss_fuse bnullable_fuse)
next
  case (ss6 a1 a2 rsa rsb rsc)
  then show ?case
    by (smt (z3) append_is_Nil_conv bmkepss1 bmkepss2 in_set_conv_decomp_first list.set_intros(1) rb_nullability set_ConsD)
qed (auto)

lemma rewrites_bmkeps: 
  assumes "r1 \<leadsto>* r2" "bnullable r1" 
  shows "bmkeps r1 = bmkeps r2"
  using assms
proof(induction r1 r2 rule: rrewrites.induct)
  case (rs1 r)
  then show "bmkeps r = bmkeps r" by simp
next
  case (rs2 r1 r2 r3)
  then have IH: "bmkeps r1 = bmkeps r2" by simp
  have a1: "bnullable r1" by fact
  have a2: "r1 \<leadsto>* r2" by fact
  have a3: "r2 \<leadsto> r3" by fact
  have a4: "bnullable r2" using a1 a2 by (simp add: rewritesnullable) 
  then have "bmkeps r2 = bmkeps r3"
    using a3 bnullable0(1) rewrite_bmkeps_aux(1) by blast 
  then show "bmkeps r1 = bmkeps r3" using IH by simp
qed


lemma rewrites_to_bsimp: 
  shows "r \<leadsto>* bsimp r"
proof (induction r rule: bsimp.induct)
  case (1 bs1 r1 r2)
  have IH1: "r1 \<leadsto>* bsimp r1" by fact
  have IH2: "r2 \<leadsto>* bsimp r2" by fact
  { assume as: "bsimp r1 = AZERO \<or> bsimp r2 = AZERO"
    with IH1 IH2 have "r1 \<leadsto>* AZERO \<or> r2 \<leadsto>* AZERO" by auto
    then have "ASEQ bs1 r1 r2 \<leadsto>* AZERO"
      by (metis bs2 continuous_rewrite rrewrites.simps star_seq2)  
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" using as by auto
  }
  moreover
  { assume "\<exists>bs. bsimp r1 = AONE bs"
    then obtain bs where as: "bsimp r1 = AONE bs" by blast
    with IH1 have "r1 \<leadsto>* AONE bs" by simp
    then have "ASEQ bs1 r1 r2 \<leadsto>* fuse (bs1 @ bs) r2" using bs3 star_seq by blast
    with IH2 have "ASEQ bs1 r1 r2 \<leadsto>* fuse (bs1 @ bs) (bsimp r2)"
      using rewrites_fuse by (meson rrewrites_trans) 
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 (AONE bs) r2)" by simp
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" by (simp add: as) 
  } 
  moreover
  { assume as1: "bsimp r1 \<noteq> AZERO" "bsimp r2 \<noteq> AZERO" and as2: "(\<nexists>bs. bsimp r1 = AONE bs)" 
    then have "bsimp_ASEQ bs1 (bsimp r1) (bsimp r2) = ASEQ bs1 (bsimp r1) (bsimp r2)" 
      by (simp add: bsimp_ASEQ1) 
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp_ASEQ bs1 (bsimp r1) (bsimp r2)" using as1 as2 IH1 IH2
      by (metis rrewrites_trans star_seq star_seq2) 
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" by simp
  } 
  ultimately show "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" by blast
next
  case (2 bs1 rs)
  have IH: "\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* bsimp x" by fact
  then have "rs s\<leadsto>* (map bsimp rs)" by (simp add: trivialbsimp_srewrites)
  also have "... s\<leadsto>* flts (map bsimp rs)" by (simp add: fltsfrewrites) 
  also have "... s\<leadsto>* distinctBy (flts (map bsimp rs)) rerase {}" by (simp add: ss6_stronger) 
  finally have "AALTs bs1 rs \<leadsto>* AALTs bs1 (distinctBy (flts (map bsimp rs)) rerase {})"
    using contextrewrites0 by auto
  also have "... \<leadsto>* bsimp_AALTs  bs1 (distinctBy (flts (map bsimp rs)) rerase {})"
    by (simp add: bsimp_AALTs_rewrites)     
  finally show "AALTs bs1 rs \<leadsto>* bsimp (AALTs bs1 rs)" by simp
qed (simp_all)


lemma to_zero_in_alt: 
  shows "AALT bs (ASEQ [] AZERO r) r2 \<leadsto> AALT bs AZERO r2"
  by (simp add: bs1 bs10 ss3)



lemma  bder_fuse_list: 
  shows "map (bder c \<circ> fuse bs1) rs1 = map (fuse bs1 \<circ> bder c) rs1"
  apply(induction rs1)
  apply(simp_all add: bder_fuse)
  done


lemma rewrite_preserves_bder: 
  shows "r1 \<leadsto> r2 \<Longrightarrow> (bder c r1) \<leadsto>* (bder c r2)"
  and   "rs1 s\<leadsto> rs2 \<Longrightarrow> map (bder c) rs1 s\<leadsto>* map (bder c) rs2"
proof(induction rule: rrewrite_srewrite.inducts)
  case (bs1 bs r2)
  then show ?case
    by (simp add: continuous_rewrite) 
next
  case (bs2 bs r1)
  then show ?case 
    apply(auto)
    apply (meson bs6 contextrewrites0 rrewrite_srewrite.bs2 rs2 ss3 ss4 sss1 sss2)
    by (simp add: r_in_rstar rrewrite_srewrite.bs2)
next
  case (bs3 bs1 bs2 r)
  then show ?case 
    apply(simp)
    
    by (metis (no_types, lifting) bder_fuse bs10 bs7 fuse_append rrewrites.simps ss4 to_zero_in_alt)
next
  case (bs4 r1 r2 bs r3)
  have as: "r1 \<leadsto> r2" by fact
  have IH: "bder c r1 \<leadsto>* bder c r2" by fact
  from as IH show "bder c (ASEQ bs r1 r3) \<leadsto>* bder c (ASEQ bs r2 r3)"
    by (metis bder.simps(5) bnullable0(1) contextrewrites1 rewrite_bmkeps_aux(1) star_seq)
next
  case (bs5 r3 r4 bs r1)
  have as: "r3 \<leadsto> r4" by fact 
  have IH: "bder c r3 \<leadsto>* bder c r4" by fact 
  from as IH show "bder c (ASEQ bs r1 r3) \<leadsto>* bder c (ASEQ bs r1 r4)"
    apply(simp)
    apply(auto)
    using contextrewrites0 r_in_rstar rewrites_fuse srewrites6 srewrites7 star_seq2 apply presburger
    using star_seq2 by blast
next
  case (bs6 bs)
  then show ?case
    using rrewrite_srewrite.bs6 by force 
next
  case (bs7 bs r)
  then show ?case
    by (simp add: bder_fuse r_in_rstar rrewrite_srewrite.bs7) 
next
  case (bs10 rs1 rs2 bs)
  then show ?case
    using contextrewrites0 by force    
next
  case ss1
  then show ?case by simp
next
  case (ss2 rs1 rs2 r)
  then show ?case
    by (simp add: srewrites7) 
next
  case (ss3 r1 r2 rs)
  then show ?case
    by (simp add: srewrites7) 
next
  case (ss4 rs)
  then show ?case
    using rrewrite_srewrite.ss4 by fastforce 
next
  case (ss5 bs1 rs1 rsb)
  then show ?case 
    apply(simp)
    using bder_fuse_list map_map rrewrite_srewrite.ss5 srewrites.simps by blast
next
  case (ss6 a1 a2 bs rsa rsb)
  then show ?case
    apply(simp only: map_append)
    by (smt (verit, best) rder_bder_rerase list.simps(8) list.simps(9) local.ss6 rrewrite_srewrite.ss6 srewrites.simps)
qed

lemma rewrites_preserves_bder: 
  assumes "r1 \<leadsto>* r2"
  shows "bder c r1 \<leadsto>* bder c r2"
using assms  
apply(induction r1 r2 rule: rrewrites.induct)
apply(simp_all add: rewrite_preserves_bder rrewrites_trans)
done


lemma central:  
  shows "bders r s \<leadsto>* bders_simp r s"
proof(induct s arbitrary: r rule: rev_induct)
  case Nil
  then show "bders r [] \<leadsto>* bders_simp r []" by simp
next
  case (snoc x xs)
  have IH: "\<And>r. bders r xs \<leadsto>* bders_simp r xs" by fact
  have "bders r (xs @ [x]) = bders (bders r xs) [x]" by (simp add: bders_append)
  also have "... \<leadsto>* bders (bders_simp r xs) [x]" using IH
    by (simp add: rewrites_preserves_bder)
  also have "... \<leadsto>* bders_simp (bders_simp r xs) [x]" using IH
    by (simp add: rewrites_to_bsimp)
  finally show "bders r (xs @ [x]) \<leadsto>* bders_simp r (xs @ [x])" 
    by (simp add: bders_simp_append)
qed

lemma main_aux: 
  assumes "bnullable (bders r s)"
  shows "bmkeps (bders r s) = bmkeps (bders_simp r s)"
proof -
  have "bders r s \<leadsto>* bders_simp r s" by (rule central)
  then 
  show "bmkeps (bders r s) = bmkeps (bders_simp r s)" using assms
    by (rule rewrites_bmkeps)
qed  




theorem main_blexer_simp: 
  shows "blexer r s = blexer_simp r s"
  unfolding blexer_def blexer_simp_def
  using b4 main_aux by simp


theorem blexersimp_correctness: 
  shows "lexer r s = blexer_simp r s"
  using blexer_correctness main_blexer_simp by simp


unused_thms

end

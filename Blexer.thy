
theory Blexer
  imports "Lexer"
begin

section \<open>Bit-Encodings\<close>

datatype bit = Z | S

fun code :: "val \<Rightarrow> bit list"
where
  "code Void = []"
| "code (Char c) = []"
| "code (Left v) = Z # (code v)"
| "code (Right v) = S # (code v)"
| "code (Seq v1 v2) = (code v1) @ (code v2)"
| "code (Stars []) = [S]"
| "code (Stars (v # vs)) =  (Z # code v) @ code (Stars vs)"

fun sz where
  "sz ZERO = 0"
| "sz ONE = 0"
| "sz (CH _) = 0"
| "sz (SEQ r1 r2) = 1 + sz r1 + sz r2"
| "sz (ALT r1 r2) = 1 + sz r1 + sz r2"
| "sz (STAR r) = 1 + sz r"
| "sz (NTIMES r n) = 1 + (n + 1) + sz r"


fun 
  Stars_add :: "val \<Rightarrow> val \<Rightarrow> val"
where
  "Stars_add v (Stars vs) = Stars (v # vs)"

function (sequential)
  decode' :: "bit list \<Rightarrow> rexp \<Rightarrow> (val * bit list)"
where
  "decode' bs ZERO = (undefined, bs)"
| "decode' bs ONE = (Void, bs)"
| "decode' bs (CH d) = (Char d, bs)"
| "decode' [] (ALT r1 r2) = (Void, [])"
| "decode' (Z # bs) (ALT r1 r2) = (let (v, bs') = decode' bs r1 in (Left v, bs'))"
| "decode' (S # bs) (ALT r1 r2) = (let (v, bs') = decode' bs r2 in (Right v, bs'))"
| "decode' bs (SEQ r1 r2) = (let (v1, bs') = decode' bs r1 in
                             let (v2, bs'') = decode' bs' r2 in (Seq v1 v2, bs''))"
| "decode' [] (STAR r) = (Void, [])"
| "decode' (S # bs) (STAR r) = (Stars [], bs)"
| "decode' (Z # bs) (STAR r) = (let (v, bs') = decode' bs r in
                                    let (vs, bs'') = decode' bs' (STAR r) 
                                    in (Stars_add v vs, bs''))"
| "decode' bs (NTIMES r n) = decode' bs (STAR r)"
by pat_completeness auto

lemma decode'_smaller:
  assumes "decode'_dom (bs, r)"
  shows "length (snd (decode' bs r)) \<le> length bs"
using assms
apply(induct bs r)
apply(auto simp add: decode'.psimps split: prod.split)
using dual_order.trans apply blast
apply (meson dual_order.trans le_SucI)
  done

termination "decode'"  
apply(relation "inv_image (measure(%cs. sz cs) <*lex*> measure(%s. size s)) (%(ds,r). (r,ds))") 
apply(auto dest!: decode'_smaller)
   apply (metis less_Suc_eq_le snd_conv)
  done

definition
  decode :: "bit list \<Rightarrow> rexp \<Rightarrow> val option"
where
  "decode ds r \<equiv> (let (v, ds') = decode' ds r 
                  in (if ds' = [] then Some v else None))"

lemma decode'_code_Stars:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> (\<forall>x. decode' (code v @ x) r = (v, x)) \<and> flat v \<noteq> []" 
  shows "decode' (code (Stars vs) @ ds) (STAR r) = (Stars vs, ds)"
  using assms
  apply(induct vs)
  apply(auto)
  done

lemma decode'_code_NTIMES:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> (\<forall>x. decode' (code v @ x) r = (v, x))" 
  shows "decode' (code (Stars vs) @ ds) (NTIMES r n) = (Stars vs, ds)"
  using assms
  apply(induct vs arbitrary: n r ds)
   apply(auto)
  done


lemma decode'_code:
  assumes "\<Turnstile> v : r"
  shows "decode' ((code v) @ ds) r = (v, ds)"
using assms
  apply(induct v r arbitrary: ds rule: Prf.induct) 
  apply(auto)[6]
  using decode'_code_Stars apply blast
  apply(rule decode'_code_NTIMES)
  apply(simp)
  apply(auto)
  done

lemma decode_code:
  assumes "\<Turnstile> v : r"
  shows "decode (code v) r = Some v"
  using assms unfolding decode_def
  by (smt append_Nil2 decode'_code old.prod.case)


section \<open>Annotated Regular Expressions\<close>

datatype arexp = 
  AZERO
| AONE "bit list"
| ACHAR "bit list" char
| ASEQ "bit list" arexp arexp
| AALTs "bit list" "arexp list"
| ASTAR "bit list" arexp
| ANTIMES "bit list" arexp nat

abbreviation
  "AALT bs r1 r2 \<equiv> AALTs bs [r1, r2]"

fun asize :: "arexp \<Rightarrow> nat" where
  "asize AZERO = 1"
| "asize (AONE cs) = 1" 
| "asize (ACHAR cs c) = 1"
| "asize (AALTs cs rs) = Suc (sum_list (map asize rs))"
| "asize (ASEQ cs r1 r2) = Suc (asize r1 + asize r2)"
| "asize (ASTAR cs r) = Suc (asize r)"
| "asize (ANTIMES cs r n) = Suc (asize r) + n"

fun 
  erase :: "arexp \<Rightarrow> rexp"
where
  "erase AZERO = ZERO"
| "erase (AONE _) = ONE"
| "erase (ACHAR _ c) = CH c"
| "erase (AALTs _ []) = ZERO"
| "erase (AALTs _ [r]) = (erase r)"
| "erase (AALTs bs (r#rs)) = ALT (erase r) (erase (AALTs bs rs))"
| "erase (ASEQ _ r1 r2) = SEQ (erase r1) (erase r2)"
| "erase (ASTAR _ r) = STAR (erase r)"
| "erase (ANTIMES _ r n) = NTIMES (erase r) n"


fun fuse :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp" where
  "fuse bs AZERO = AZERO"
| "fuse bs (AONE cs) = AONE (bs @ cs)" 
| "fuse bs (ACHAR cs c) = ACHAR (bs @ cs) c"
| "fuse bs (AALTs cs rs) = AALTs (bs @ cs) rs"
| "fuse bs (ASEQ cs r1 r2) = ASEQ (bs @ cs) r1 r2"
| "fuse bs (ASTAR cs r) = ASTAR (bs @ cs) r"
| "fuse bs (ANTIMES cs r n) = ANTIMES (bs @ cs) r n"

lemma fuse_append:
  shows "fuse (bs1 @ bs2) r = fuse bs1 (fuse bs2 r)"
  apply(induct r)
  apply(auto)
  done


fun intern :: "rexp \<Rightarrow> arexp" where
  "intern ZERO = AZERO"
| "intern ONE = AONE []"
| "intern (CH c) = ACHAR [] c"
| "intern (ALT r1 r2) = AALT [] (fuse [Z] (intern r1)) 
                                (fuse [S]  (intern r2))"
| "intern (SEQ r1 r2) = ASEQ [] (intern r1) (intern r2)"
| "intern (STAR r) = ASTAR [] (intern r)"
| "intern (NTIMES r n) = ANTIMES [] (intern r) n"


fun retrieve :: "arexp \<Rightarrow> val \<Rightarrow> bit list" where
  "retrieve (AONE bs) Void = bs"
| "retrieve (ACHAR bs c) (Char d) = bs"
| "retrieve (AALTs bs [r]) v = bs @ retrieve r v"
| "retrieve (AALTs bs (r#rs)) (Left v) = bs @ retrieve r v"
| "retrieve (AALTs bs (r#rs)) (Right v) = bs @ retrieve (AALTs [] rs) v"
| "retrieve (ASEQ bs r1 r2) (Seq v1 v2) = bs @ retrieve r1 v1 @ retrieve r2 v2"
| "retrieve (ASTAR bs r) (Stars []) = bs @ [S]"
| "retrieve (ASTAR bs r) (Stars (v#vs)) = 
     bs @ [Z] @ retrieve r v @ retrieve (ASTAR [] r) (Stars vs)"
| "retrieve (ANTIMES bs r 0) (Stars []) = bs @ [S]"
| "retrieve (ANTIMES bs r (Suc n)) (Stars (v#vs)) = 
     bs @ [Z] @ retrieve r v @ retrieve (ANTIMES [] r n) (Stars vs)"


fun
 bnullable :: "arexp \<Rightarrow> bool"
where
  "bnullable (AZERO) = False"
| "bnullable (AONE bs) = True"
| "bnullable (ACHAR bs c) = False"
| "bnullable (AALTs bs rs) = (\<exists>r \<in> set rs. bnullable r)"
| "bnullable (ASEQ bs r1 r2) = (bnullable r1 \<and> bnullable r2)"
| "bnullable (ASTAR bs r) = True"
| "bnullable (ANTIMES bs r n) = (if n  = 0 then True else bnullable r)"

abbreviation
  bnullables :: "arexp list \<Rightarrow> bool"
where
  "bnullables rs \<equiv> (\<exists>r \<in> set rs. bnullable r)"

function (sequential)
  bmkeps :: "arexp \<Rightarrow> bit list" 
where
  "bmkeps(AONE bs) = bs"
| "bmkeps(ASEQ bs r1 r2) = bs @ (bmkeps r1) @ (bmkeps r2)"
| "bmkeps(AALTs bs (r#rs)) = 
    (if bnullable(r) then (bs @ bmkeps r) else (bmkeps (AALTs bs rs)))"
| "bmkeps(ASTAR bs r) = bs @ [S]"
| "bmkeps(ANTIMES bs r n) = 
    (if n = 0 then bs @ [S] else bs @ [Z] @ (bmkeps r) @ bmkeps(ANTIMES [] r (n - 1)))"
apply(pat_completeness)
apply(auto)
done

termination "bmkeps"  
apply(relation "measure asize") 
        apply(auto)
  using asize.elims by force

fun
   bmkepss :: "arexp list \<Rightarrow> bit list"
where
  "bmkepss (r # rs) = (if bnullable(r) then (bmkeps r) else (bmkepss rs))"


lemma bmkepss1:
  assumes "\<not> bnullables rs1"
  shows "bmkepss (rs1 @ rs2) = bmkepss rs2"
  using assms
  by(induct rs1) (auto)
  

lemma bmkepss2:
  assumes "bnullables rs1"
  shows "bmkepss (rs1 @ rs2) = bmkepss rs1"
  using assms
  by (induct rs1) (auto)


fun
 bder :: "char \<Rightarrow> arexp \<Rightarrow> arexp"
where
  "bder c (AZERO) = AZERO"
| "bder c (AONE bs) = AZERO"
| "bder c (ACHAR bs d) = (if c = d then AONE bs else AZERO)"
| "bder c (AALTs bs rs) = AALTs bs (map (bder c) rs)"
| "bder c (ASEQ bs r1 r2) = 
     (if bnullable r1
      then AALT bs (ASEQ [] (bder c r1) r2) (fuse (bmkeps r1) (bder c r2))
      else ASEQ bs (bder c r1) r2)"
| "bder c (ASTAR bs r) = ASEQ (bs @ [Z]) (bder c r) (ASTAR [] r)"
| "bder c (ANTIMES bs r n) = (if n = 0 then AZERO else ASEQ (bs @ [Z]) (bder c r) (ANTIMES [] r (n - 1)))"

fun 
  bders :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders r [] = r"
| "bders r (c#s) = bders (bder c r) s"

lemma bders_append:
  "bders c (s1 @ s2) = bders (bders c s1) s2"
  apply(induct s1 arbitrary: c s2)
  apply(simp_all)
  done

lemma bnullable_correctness:
  shows "nullable (erase r) = bnullable r"
  apply(induct r rule: erase.induct)
  apply(simp_all)
  done

lemma erase_fuse:
  shows "erase (fuse bs r) = erase r"
  apply(induct r rule: erase.induct)
  apply(simp_all)
  done

lemma erase_intern [simp]:
  shows "erase (intern r) = r"
  apply(induct r)
  apply(simp_all add: erase_fuse)
  done

lemma erase_bder [simp]:
  shows "erase (bder a r) = der a (erase r)"
  apply(induct r rule: erase.induct)
  apply(simp_all add: erase_fuse bnullable_correctness)
  done

lemma erase_bders [simp]:
  shows "erase (bders r s) = ders s (erase r)"
  apply(induct s arbitrary: r )
  apply(simp_all)
  done

lemma bnullable_fuse:
  shows "bnullable (fuse bs r) = bnullable r"
  apply(induct r arbitrary: bs)
  apply(auto)
  done

lemma retrieve_encode_STARS:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
  shows "code (Stars vs) = retrieve (ASTAR [] (intern r)) (Stars vs)"
  using assms
  apply(induct vs)
  apply(simp_all)
  done

lemma retrieve_encode_NTIMES:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> code v = retrieve (intern r) v" "length vs = n"
  shows "code (Stars vs) = retrieve (ANTIMES [] (intern r) n) (Stars vs)"
  using assms
  apply(induct vs arbitrary: n)
   apply(simp_all)
  by force


lemma retrieve_fuse2:
  assumes "\<Turnstile> v : (erase r)"
  shows "retrieve (fuse bs r) v = bs @ retrieve r v"
  using assms
  apply(induct r arbitrary: v bs)
  apply(auto elim: Prf_elims)[4]
  apply(case_tac x2a)
  apply(simp)
  using Prf_elims(1) apply blast
  apply(case_tac x2a)
  apply(simp)
  apply(simp)
  apply(case_tac list)
  apply(simp)
  apply(simp)
  apply (smt (verit, best) Prf_elims(3) append_assoc retrieve.simps(4) retrieve.simps(5))
  apply(simp)
  using retrieve_encode_STARS
  apply(auto elim!: Prf_elims)[1]
  apply(case_tac vs)
  apply(simp)
   apply(simp)
  (* NTIMES *)
  apply(auto elim!: Prf_elims)[1]
  apply(case_tac vs1)
   apply(simp_all)
  apply(case_tac vs2)
   apply(simp_all)
  done

lemma retrieve_fuse:
  assumes "\<Turnstile> v : r"
  shows "retrieve (fuse bs (intern r)) v = bs @ retrieve (intern r) v"
  using assms 
  by (simp_all add: retrieve_fuse2)


lemma retrieve_code:
  assumes "\<Turnstile> v : r"
  shows "code v = retrieve (intern r) v"
  using assms
  apply(induct v r )
        apply(simp_all add: retrieve_fuse retrieve_encode_STARS)
  apply(subst retrieve_encode_NTIMES)
    apply(auto)
  done 
 


lemma retrieve_AALTs_bnullable1:
  assumes "bnullable r"
  shows "retrieve (AALTs bs (r # rs)) (mkeps (erase (AALTs bs (r # rs))))
         = bs @ retrieve r (mkeps (erase r))"
  using assms
  apply(case_tac rs)
  apply(auto simp add: bnullable_correctness)
  done

lemma retrieve_AALTs_bnullable2:
  assumes "\<not>bnullable r" "bnullables rs"
  shows "retrieve (AALTs bs (r # rs)) (mkeps (erase (AALTs bs (r # rs))))
         = retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
  using assms
  apply(induct rs arbitrary: r bs)
  apply(auto)
  using bnullable_correctness apply blast
  apply(case_tac rs)
  apply(auto)
  using bnullable_correctness apply blast
  apply(case_tac rs)
  apply(auto)
  done

lemma bmkeps_retrieve_AALTs: 
  assumes "\<forall>r \<in> set rs. bnullable r \<longrightarrow> bmkeps r = retrieve r (mkeps (erase r))" 
          "bnullables rs"
  shows "bs @ bmkepss rs = retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
 using assms
  apply(induct rs arbitrary: bs)
  apply(auto)
  using retrieve_AALTs_bnullable1 apply presburger
  apply (metis retrieve_AALTs_bnullable2)
  apply (simp add: retrieve_AALTs_bnullable1)
  by (metis retrieve_AALTs_bnullable2)

lemma bmkeps_retrieve_ANTIMES: 
  assumes "if n = 0 then True else bmkeps r = retrieve r (mkeps (erase r))" 
  and     "bnullable (ANTIMES bs r n)"
  shows "bmkeps (ANTIMES bs r n) = retrieve (ANTIMES bs r n) (Stars (replicate n (mkeps (erase r))))"
 using assms
  apply(induct n arbitrary: r bs)
  apply(auto)[1]
  apply(simp)
  done

lemma bmkeps_retrieve:
  assumes "bnullable r"
  shows "bmkeps r = retrieve r (mkeps (erase r))"
  using assms
  apply(induct r rule: bmkeps.induct)
        apply(auto)
  apply (simp add: retrieve_AALTs_bnullable1)
  using retrieve_AALTs_bnullable1 apply force
  apply(metis retrieve_AALTs_bnullable2)
  by (metis Cons_eq_appendI One_nat_def Suc_diff_1 eq_Nil_appendI replicate_Suc retrieve.simps(10))  
  

lemma bder_retrieve:
  assumes "\<Turnstile> v : der c (erase r)"
  shows "retrieve (bder c r) v = retrieve r (injval (erase r) c v)"
  using assms  
  apply(induct r arbitrary: v rule: erase.induct)
  using Prf_elims(1) apply auto[1]
  using Prf_elims(1) apply auto[1]
  apply(auto)[1]
  apply (metis Prf_elims(4) injval.simps(1) retrieve.simps(1) retrieve.simps(2))
  using Prf_elims(1) apply blast
  (* AALTs case *)
  apply(simp)
  apply(erule Prf_elims)
  apply(simp)
  apply(simp)
  apply(rename_tac "r\<^sub>1" "r\<^sub>2" rs v)
  apply(erule Prf_elims)
  apply(simp)
  apply(simp)
  apply(case_tac rs)
  apply(simp)
  apply(simp)
  using Prf_elims(3) apply fastforce
  (* ASEQ case *) 
  apply(simp)
  apply(case_tac "nullable (erase r1)")
  apply(simp)
  apply(erule Prf_elims)
  using Prf_elims(2) bnullable_correctness apply force
  apply (simp add: bmkeps_retrieve bnullable_correctness retrieve_fuse2)
  apply (simp add: bmkeps_retrieve bnullable_correctness retrieve_fuse2)
  using Prf_elims(2) apply force
  (* ASTAR case *)  
  apply(rename_tac bs r v)
  apply(simp)  
  apply(erule Prf_elims)
  apply(clarify)
  apply(erule Prf_elims)
  apply(clarify)
   apply (simp add: retrieve_fuse2)
  (* ANTIMES case *)
  apply(auto)  
  apply(erule Prf_elims)
  apply(erule Prf_elims)
  apply(clarify)
  apply(erule Prf_elims)
  apply(clarify)
  by (metis (full_types) Suc_pred append_assoc injval.simps(8) retrieve.simps(10) retrieve.simps(6))


lemma MAIN_decode:
  assumes "\<Turnstile> v : ders s r"
  shows "Some (flex r id s v) = decode (retrieve (bders (intern r) s) v) r"
  using assms
proof (induct s arbitrary: v rule: rev_induct)
  case Nil
  have "\<Turnstile> v : ders [] r" by fact
  then have "\<Turnstile> v : r" by simp
  then have "Some v = decode (retrieve (intern r) v) r"
    using decode_code retrieve_code by auto
  then show "Some (flex r id [] v) = decode (retrieve (bders (intern r) []) v) r"
    by simp
next
  case (snoc c s v)
  have IH: "\<And>v. \<Turnstile> v : ders s r \<Longrightarrow> 
     Some (flex r id s v) = decode (retrieve (bders (intern r) s) v) r" by fact
  have asm: "\<Turnstile> v : ders (s @ [c]) r" by fact
  then have asm2: "\<Turnstile> injval (ders s r) c v : ders s r" 
    by (simp add: Prf_injval ders_append)
  have "Some (flex r id (s @ [c]) v) = Some (flex r id s (injval (ders s r) c v))"
    by (simp add: flex_append)
  also have "... = decode (retrieve (bders (intern r) s) (injval (ders s r) c v)) r"
    using asm2 IH by simp
  also have "... = decode (retrieve (bder c (bders (intern r) s)) v) r"
    using asm by (simp_all add: bder_retrieve ders_append)
  finally show "Some (flex r id (s @ [c]) v) = 
                 decode (retrieve (bders (intern r) (s @ [c])) v) r" by (simp add: bders_append)
qed

definition blexer where
 "blexer r s \<equiv> if bnullable (bders (intern r) s) then 
                decode (bmkeps (bders (intern r) s)) r else None"

lemma blexer_correctness:
  shows "blexer r s = lexer r s"
proof -
  { define bds where "bds \<equiv> bders (intern r) s"
    define ds  where "ds \<equiv> ders s r"
    assume asm: "nullable ds"
    have era: "erase bds = ds" 
      unfolding ds_def bds_def by simp
    have mke: "\<Turnstile> mkeps ds : ds"
      using asm by (simp add: mkeps_nullable)
    have "decode (bmkeps bds) r = decode (retrieve bds (mkeps ds)) r"
      using bmkeps_retrieve
      using asm era
      using bnullable_correctness by force 
    also have "... =  Some (flex r id s (mkeps ds))"
      using mke by (simp_all add: MAIN_decode ds_def bds_def)
    finally have "decode (bmkeps bds) r = Some (flex r id s (mkeps ds))" 
      unfolding bds_def ds_def .
  }
  then show "blexer r s = lexer r s"
    unfolding blexer_def lexer_flex
    by (auto simp add: bnullable_correctness[symmetric])
qed


unused_thms

end

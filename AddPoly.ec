require Poly Bilinear.
require import Group List AddList Ring AllCore IntDiv Bigalg DList DProd Distr AddDistr.

  (* List libary is intended to extend the basic polynomial libary
  for the specific case where the coeff are the exponents to a
  prime order cyclic group *)
theory AddPoly.

clone Bilinear.Bl as Bl.
  
import Bl.

clone IDomain as R with
  type t <= GP.exp,
  op zeror <= GP.ZModE.zero,
  op oner <= GP.ZModE.one,
  op   ( + ) <= GP.ZModE.( + ),
  op   [ - ] <= GP.ZModE.([-]),
  op   ( * ) <= GP.ZModE.( * ),
  op   invr  <= GP.ZModE.inv,
  pred   unit <= fun x => (x <>  GP.ZModE.zero),
  lemma addrA <=  GP.ZModE.ZModpField.addrA,
  lemma addrC  <= GP.ZModE.ZModpField.addrC,
  lemma add0r <=  GP.ZModE.ZModpField.add0r,
  lemma addNr <=  GP.ZModE.ZModpField.addNr,
  lemma mulrA <=  GP.ZModE.ZModpField.mulrA,
  lemma mulrC <=  GP.ZModE.ZModpField.mulrC,
  lemma mul1r <=  GP.ZModE.ZModpField.mul1r,
  lemma mulrDl <= GP.ZModE.ZModpField.mulrDl,
  lemma oner_neq0 <= GP.ZModE.ZModpField.oner_neq0,
  lemma mulVr <= GP.ZModE.ZModpField.mulVr,
  lemma unitP <= GP.ZModE.ZModpField.unitP,
  lemma unitout <= GP.ZModE.ZModpField.unitout,
  lemma mulf_eq0 <= GP.ZModE.ZModpField.mulf_eq0.
     
clone Poly.Poly as BasePoly with
  type coeff <- GP.exp,
 theory IDCoeff <- R.

 import BasePoly.
 import R.

 
  op prepolyCn (k   : int, c : GP.exp) = fun i => if 0 <= k /\ i = k then c else zeror.
  lemma ispolyCn (k : int, c : GP.exp) : BasePoly.ispoly (prepolyCn k c).
      proof.
      split=> @/prepolyCn [l lt0_l|].
        + case: (0 <= k); move => h; smt(@Int).
        + exists k => l gt1_l. smt(@Int).
    qed.
    
    op polyCn k c = BasePoly.to_polyd (prepolyCn k c).

      
  lemma polyCnE k c i : (polyCn k c).[i] = if 0 <= k /\ i = k then c else zeror.
      by rewrite coeffE 1:ispolyCn. qed.
    
  lemma deg_polyCn c i: c <> zeror => 0 <= i => deg (polyCn i c) = i + 1.
  proof.
      move => h h'. apply/degP=> //=; trivial. smt(). rewrite polyCnE. smt().
      move => i' hi. rewrite polyCnE. smt().
  qed.

  lemma lc_polyCn c i : 0 <= i => lc (polyCn i c) = c.
  proof.
    move => h. rewrite polyCnE. rewrite h. simplify. case (c = zeror) => h'. subst. smt(). rewrite deg_polyCn; trivial.
  qed.

     lemma foldr_mkseq_bigi_eq f : forall j, 0 <= j => BigCf.BCA.bigi predT f 0 j =
       foldr R.(+) zeror (mkseq f j).
   proof.
     apply intind. simplify. move => @/bigi @/range. simplify. rewrite iota0. smt(). rewrite BigCf.BCA.big_nil. simplify.
     smt(@List).
     (* inductive case *)
     move => i ip ind_hyp. simplify. rewrite mkseqS. smt(). rewrite foldr_rcons. simplify.
     have : f i + zeror = zeror + f i. smt(@GP.ZModE).  move => g. rewrite g. rewrite foldr_const. smt(@GP.ZModE).
     smt(@GP.ZModE). rewrite -ind_hyp. move => @/bigi @/range. simplify. rewrite iotaSr. smt(). rewrite BigCf.BCA.big_rcons.
     simplify. have : predT i = true. smt(). move => g'. rewrite g'. simplify. smt(@GP.ZModE).
   qed.
    
  lemma polyMCnE_0 p c : (p * polyCn 1 c).[0] = zeror.
  proof.
    rewrite polyME. rewrite  foldr_mkseq_bigi_eq. smt(). simplify. rewrite mkseq1. simplify. rewrite polyCnE.
    smt(@GP.ZModE).
  qed.

  lemma  polyMCn_deg p c : c <> zeror => p <> poly0 => deg (p * polyCn 1 c) = deg p + 1.
  proof.
    move => h h'. rewrite degM_proper. apply mulf_neq0. smt(lc_eq0). rewrite lc_polyCn. smt(). trivial.
    rewrite deg_polyCn; trivial.
  qed.

  lemma polyCn_poly0 i : polyCn i zeror = poly0.
  proof.
    apply poly_eqP => c hc. rewrite polyCnE. case(0 <= i /\ c =i) => h. smt(poly0E). smt(poly0E). 
qed.

  (* Intro a construction which builds a poynomial of order 2 or less, which is used for lagrange inter.  *)
  op prepolyD2 (c1 c0 : GP.exp) = fun i => if i = 0 then c0 else (if i = 1 then c1 else zeror).
  lemma ispolyD2 (c1 c0 : GP.exp) : BasePoly.ispoly (prepolyD2 c0 c1).
      proof.
      split=> @/prepolyD2 [l lt0_l|].
        + smt(@Int).
        + exists 1 => l gt1_l. smt(@Int).
    qed.
    
  op polyD2 c1 c0 = BasePoly.to_polyd (prepolyD2 c1 c0).
    
   lemma polyD2E c1 c0 i : (polyD2 c1 c0).[i] =  if i = 0 then c0 else (if i = 1 then c1 else zeror).
       by rewrite coeffE 1:ispolyD2. qed.
     
  lemma deg_polyD2 c1 c0 : c1 <> zeror => deg (polyD2 c1 c0) = 2.
  proof.
    move => h. apply/degP=> //=; trivial. rewrite polyD2E. smt().
      move => i' hi. rewrite polyD2E. smt().
qed.

  lemma deg_leq_polyD2 c1 c0 : deg (polyD2 c1 c0) <= 2.
  proof.
    apply deg_leP. smt(). move => i hi. rewrite polyD2E. have : i <> 0. smt(). move => g. have : i <> 1. smt(). move => g'.
    rewrite g g'. simplify. trivial.
  qed.

  lemma lc_polyD2 c1 c0 : c1 <> zeror => lc (polyD2 c1 c0) = c1.
  proof.
    move => h. rewrite polyD2E. rewrite deg_polyD2; trivial.
  qed.
 
  lemma  polyMD2_deg p c1 c0 : c1 <> zeror => p <> poly0 => deg (p * polyD2 c1 c0) = deg p + 1.
  proof.
    move => h h'. rewrite degM_proper. apply mulf_neq0. smt(lc_eq0). rewrite lc_polyD2; trivial. 
    rewrite deg_polyD2; trivial.
  qed.

  lemma polyMD2_0 p c1 c0 : (p * polyD2 c1 c0).[0] = p.[0] * c0.
  proof.
    rewrite polyME. rewrite  foldr_mkseq_bigi_eq. smt(). simplify. rewrite mkseq1. simplify. rewrite polyD2E.
    simplify. smt(@R).
  qed.

  lemma polyD2_polyC c0 : polyD2 zeror c0 = polyC c0. 
  proof.
    apply poly_eqP => c hc. rewrite polyCE polyD2E. smt().
  qed.
  
  (* Inital poly lemmas *)

 lemma peval_simp (m :poly) a :
    peval m a = foldr ( + )%R zeror
      (mkseq (fun i => ( * )  m.[i] (exp a i))
        (deg m + 1)).
   proof.
     move => @/peval @/big. apply eq_foldr; trivial. apply (eq_from_nth zeror).
     smt(@List). move => i h. rewrite filter_predT. rewrite filter_predT in h.
     rewrite size_map in h. rewrite size_range in h. rewrite nth_mkseq. smt().
     rewrite nth_mkseq. smt(). smt().
 qed.

  lemma peval_simp_gen (m :poly) a j : deg m <= j =>
    peval m a = foldr ( + )%R zeror
      (mkseq (fun i => ( * )  m.[i] (exp a i)) j).
   proof.
     move => h. move => @/peval @/big. apply eq_foldr_trunc; trivial. smt(@R). smt(@R). smt(@R).
     move => i hi.
     (* case where the exp is non-zero *)
     case (i < deg m) => g. rewrite (nth_mkseq). smt(@List). rewrite (nth_map 0). smt(@List). simplify. smt(@List).
     case (i = deg m) => g'. rewrite (nth_map 0). smt(@List).  case(j = deg m) => g''. rewrite eq_sym. rewrite nth_default.
     smt(@List). rewrite gedeg_coeff. smt(@List). smt(@R). rewrite nth_mkseq. smt(). simplify. smt(@List). rewrite nth_mkseq.
     smt(@List). rewrite (nth_default). smt(@List). simplify. rewrite gedeg_coeff. smt(). smt(@R).
  qed.
 
  lemma polyL0 :polyL [] = poly0.
    proof.
      apply poly_eqP. move => c h. rewrite polyCE. rewrite polyLE. smt(@BasePoly). 
    qed.

  (* If you evaluate the zero polnomial at any point you get zero *)
  lemma peval0 a : peval poly0 a = zeror.
  proof.    
    move => @/peval. rewrite BigCf.BCA.big1. move => i h.
    simplify. rewrite poly0E. smt(@R). smt(@R).
  qed.

  lemma exp_dumb : forall i, 0 <= i => exp zeror (1 + i) = zeror.
  proof.
    apply intind. smt(expr1). move => i g0 h. simplify. have : i +2 = i + 1 + 1. smt(). move => g. rewrite g.
    rewrite exprS. smt(). smt(@GP.ZModE).
qed.

  
  lemma degD_proper p q :
      lc p + lc q <> zeror => deg (p+q) = max (deg p)(deg q).
  proof.
    move => h. apply degP; smt(@BasePoly).
  qed.

  lemma degD_inproper (p q : poly) : deg (p+ q) <> max (deg p) (deg q) => deg p = deg q /\ lc p + lc q = zeror.
   proof.
     move => h. have : deg p = deg q. smt(@BasePoly). move => h'. split. trivial. smt(@BasePoly).
 qed.

  lemma peval_id p : peval p zeror = p.[0].
   proof.    
     rewrite peval_simp. rewrite mkseqSr. smt(@BasePoly). simplify.  rewrite foldr_id.
     smt(@GP.ZModE). rewrite (all_nth _ GP.ZModE.zero).
     move => i h. simplify. rewrite nth_mkseq. smt(@List). move => @/(\o). rewrite exp_dumb. smt(@List).
     smt(@GP.ZModE). rewrite expr0. smt(@GP.ZModE).
  qed.

  lemma peval_polyC a b : peval (polyC a) b = a.
  proof.
    rewrite peval_simp. case (a = zeror); move => h. have : deg (polyC a) = 0. smt(@BasePoly).
    move => h'. rewrite h'. rewrite mkseq1. simplify. smt(@BasePoly @GP.ZModE).
    have : deg (polyC a) = 1. smt(@BasePoly). move => h'. rewrite h'. rewrite mkseqS. smt().
    rewrite mkseq1. simplify. rewrite polyCE. rewrite polyCE. simplify. rewrite expr0. smt(@BasePoly @GP.ZModE).
  qed.

  lemma polyC_peval p i : deg p < 2 => polyC (peval p i) = p.
  proof.
    move => h. apply poly_eqP. move => c hc. rewrite polyCE. rewrite peval_simp. case (c = 0) => h'. case (deg p = 1) => h''.
    rewrite h''. rewrite mkseqS. smt(). rewrite mkseq1. simplify. subst. rewrite (gedeg_coeff _ 1). smt().
    smt(@R). have : deg p = 0. smt(ge0_deg @Int). move => h'''. rewrite h'''. simplify.  rewrite mkseq1. simplify.  subst.
    smt(@R). rewrite gedeg_coeff. smt(). trivial.
  qed.
    
  lemma peval_X a : peval X a = a.
  proof.
    rewrite peval_simp. have : deg (X) = 2. smt(@BasePoly). move => h. rewrite h.
    rewrite mkseqS. smt(). have : 2 = 1 + 1. smt(). move => h''. rewrite h''. rewrite mkseqS. smt(). rewrite mkseq1.
    simplify. rewrite polyXE. rewrite polyXE. rewrite polyXE. simplify. rewrite expr1. smt(@GP.ZModE).
  qed.

  
  lemma peval_add_sub i j :  forall p p' a, i = deg p => j = deg p' => peval p a + peval p' a = peval (p + p') a.
  proof.
    wlog: i j / i <= j => [wlog p p' a h h'|le_ij]. case (i <= j); move => g. apply (wlog i j); trivial.
    have : p + p' = p' + p. smt(@BasePoly). move => g'. rewrite g'. rewrite -(wlog j i); trivial. smt().  smt(@GP.ZModE).
    (* we have discharged the general principial and now need to show the base case holds *)
     move => p p' a h h'. rewrite peval_simp. rewrite peval_simp. rewrite peval_simp. rewrite foldr_add_distr_sub.
    smt(@GP.ZModE). smt(@GP.ZModE).   smt(@GP.ZModE). smt(@List).
    rewrite size_mkseq. rewrite size_mkseq. apply eq_foldr_trunc.   smt(@GP.ZModE).   smt(@GP.ZModE).   smt(@GP.ZModE).
    move => i0 h''. rewrite size_mkseq in h''.
    rewrite size_mkseq in h''. simplify. case (deg (p+p') = max (deg p)(deg p')); move => h'''.
    (* main case *)
    rewrite nth_mkseq. smt(@Int @BasePoly). rewrite nth_mkseq. smt(@Int). simplify.
    rewrite polyDE. case (i0 < deg p + 1); move => g. rewrite nth_mkseq. smt(). rewrite nth_mkseq. smt(). simplify.
    smt(@GP.ZModE). rewrite nth_default. smt(@List). rewrite nth_mkseq. smt(@Int @BasePoly). simplify.
    rewrite (gedeg_coeff p). smt(). smt(@GP.ZModE).
    (* annyoing case *)
    have : deg (p + p') <> max (deg p) (deg p'). trivial. move => g. apply degD_inproper in h'''. rewrite nth_mkseq.
    smt(@BasePoly). simplify. rewrite nth_mkseq. smt(@BasePoly). rewrite nth_mkseq. smt(@BasePoly). simplify.
    case (i0 < deg(p + p') + 1); move => g'. rewrite nth_mkseq. smt(). smt(@BasePoly @GP.ZModE).
    rewrite nth_default. smt(@List). have : (p + p').[i0] = zeror. smt(@BasePoly @GP.ZModE). move => g''.
    have : p.[i0] * exp a i0 + p'.[i0] * exp a i0 = (p.[i0] + p'.[i0]) * exp a i0. smt(@GP.ZModE). move => g'''. rewrite g'''.
    smt(@BasePoly @GP.ZModE).
qed.

  lemma peval_add p p' a : peval p a + peval p' a = peval (p + p') a.
    apply (peval_add_sub (deg p)(deg p')); trivial.
    qed.
    
  lemma peval_mul p a b : peval p a * b = peval (b ** p) a.
  proof.
    rewrite !peval_simp. rewrite dis_mul_add. smt(@GP.ZModE). smt(@GP.ZModE). apply foldr_eq_partR. smt(@GP.ZModE).
    smt(@GP.ZModE). smt(@GP.ZModE). smt(@GP.ZModE). smt(@List @BasePoly). apply (eq_from_nth zeror).
    smt(@List @BasePoly). move => i hi. rewrite size_mkseq in hi. rewrite nth_mkseq. smt(@BasePoly).
    rewrite nth_take. smt(@List @BasePoly).  smt(@List @BasePoly). rewrite (nth_map zeror).  smt(@List @BasePoly).
    rewrite nth_mkseq.  smt(@List @BasePoly).  simplify. rewrite polyZE. smt(@GP.ZModE).
    apply (all_nth _ zeror). move => i hi.  rewrite size_drop in hi. smt(@List @BasePoly). rewrite size_map in hi.
    rewrite !size_mkseq in hi. rewrite nth_drop. smt(@List @BasePoly). smt(). simplify. rewrite (nth_map zeror).
    smt(@List @BasePoly). rewrite nth_mkseq. smt(@List @BasePoly). rewrite size_mkseq. simplify.
    case (b = zeror) => g. smt(@GP.ZModE). rewrite gedeg_coeff. rewrite scalepE.
    have : deg (polyC b * p) = deg p. rewrite degM_proper. smt(@BasePoly @GP.ZModE). smt(@BasePoly).
    move => h.  rewrite h. smt(). smt(@GP.ZModE).
  qed.

  lemma poly_sum_nth x i : (foldr BasePoly.(+) poly0 x).[i] =
   foldr R.(+) zeror (map (fun p=> p.[i]) x).
  proof.
    elim x. simplify. smt(@BasePoly). move => x l ind_hyp. simplify. rewrite -ind_hyp. smt(@BasePoly).
  qed.
  
  lemma peval_sum phis x : peval (foldr BasePoly.(+) poly0 phis) x = foldr R.(+) zeror (map (fun phi => peval phi x) phis).
  proof.
    elim phis. simplify. apply peval0. move => x0 l ind_hyp. simplify. rewrite -peval_add. smt().
  qed.
  
  lemma peval_neg_sub p a : - peval (polyL p) a = peval (-(polyL p)) a.
  proof.
    rewrite peval_simp. rewrite peval_simp.
    have : mkseq (fun (i : int) => (- polyL p).[i] * exp a i) (deg (- polyL p) + 1) =
    map (fun (a : GP.exp) => - a) (mkseq (fun i => (polyL p).[i] * exp a i) (deg (polyL p) + 1)).
    apply (eq_from_nth zeror). smt(@List @BasePoly). move => i h. rewrite (nth_map zeror).
    smt(@List @BasePoly). rewrite nth_mkseq. smt(@BasePoly @List). rewrite nth_mkseq.
    smt(@List @BasePoly). simplify. rewrite polyLE. rewrite polyNE. rewrite polyLE.
    smt(@GP.ZModE). move => h. rewrite h. apply dis_neg; smt(@GP.ZModE).
  qed.

  lemma peval_neg p a : - peval p a = peval (-p) a.
  proof.
    elim (surj_polyL p (deg p)). move => s h. rewrite h. apply peval_neg_sub.
  qed.

  lemma Xi_eval i a : peval (X - polyC i) a = a - i. rewrite -polyCN. rewrite -peval_add.
    rewrite peval_X. rewrite peval_polyC. smt(@GP.ZModE).
    qed.

  
   lemma peval_polyM_X p a: peval (p * X) a = peval p a * a.
   proof.
      case (p = poly0); move => h.
     (* stupid case *)
     rewrite h. smt(peval0 @BasePoly @GP.ZModE).
     (* resume *)
     rewrite peval_simp. rewrite peval_simp. rewrite mkseqSr. smt(@BasePoly). simplify.
     have : forall b, (p * X).[0] * exp a 0 + b = b. rewrite expr0. have :  (p * X).[0] = zeror. smt(@BasePoly @GP.ZModE).
     move => h'. rewrite h'. smt(@GP.ZModE). move => h'. rewrite h'. rewrite dis_mul_add. smt(@GP.ZModE). smt(@GP.ZModE).
     apply eq_foldr; trivial. apply (eq_from_nth zeror). smt(@List @BasePoly). move => i ip. rewrite nth_mkseq. smt(@List).
     rewrite (nth_map zeror). smt(@List @BasePoly). rewrite nth_mkseq. smt(@List @BasePoly). move => @/(\o). simplify.
     rewrite polyMXE. have : 1 + i = i + 1. smt(). move => g. rewrite g. rewrite exprS. smt(). smt(@GP.ZModE).
 qed.

 lemma polyM_polyCn p c i : 0 <= i => (p * polyCn 1 c).[i + 1] = p.[i] * c.
 proof.
   move => h. rewrite polyME. rewrite foldr_mkseq_bigi_eq. smt(). rewrite (foldr_id_nth_mkseq _ _ _ i). smt(@GP.ZModE).
   smt(@GP.ZModE). smt(@GP.ZModE). smt().
   apply (all_nth _ zeror) => i0 hi0. rewrite nth_mkseq. smt(@List). simplify. rewrite polyCnE. smt(@R @List).
   apply (all_nth _ zeror) => i0 hi0. rewrite nth_mkseq. smt(@List). simplify. rewrite polyCnE. smt(@R @List).
   simplify. smt(polyCnE).
 qed.

lemma polyM_polyD2 p c1 c0 i : 0 <= i => c1 <> zeror => (p * polyD2 c1 c0).[i + 1] =
    (p.[i] * c1) + (p.[i + 1] * (polyD2 c1 c0).[0]).
 proof.
   move => h h'. rewrite polyME. rewrite foldr_mkseq_bigi_eq. smt(). rewrite mkseqS. smt(). rewrite mkseqS. smt(). 
 move => @/(\o). simplify. rewrite !foldr_rcons. have : forall a b, foldr R.(+) a b = a + (foldr R.(+) zeror b). move => a b.
   elim b. smt(@R). move => x l ind_hyp. smt(@R).
   move => g. rewrite g.  rewrite foldr_id. smt(@GP.ZModE). apply (all_nth _ zeror) => i0 hi0. rewrite nth_mkseq. smt(@List).
   simplify. rewrite polyD2E. smt(@R @List). rewrite polyD2E. simplify. have : i + 1 - i <> 0. smt(). move => g'. rewrite !g'.
   have : i + 1 - i = 1. smt(). move => g''. rewrite g''. simplify. smt(@R).
 qed.
     
 lemma peval_polyM_polyCn p c a: peval (p * (polyCn 1 c)) a = peval p a * a * c.
   proof.
     case (p = poly0); move => h.
     (* stupid case *)
     rewrite h. smt(peval0 @BasePoly @GP.ZModE).
     (* second stupid case *)
     case (c = zeror) => h'. subst. rewrite polyCn_poly0. rewrite IDPoly.mulrC. rewrite mul0p. rewrite peval0. smt(@R).
     (* resume *)
     rewrite peval_simp. rewrite peval_simp. rewrite polyMCn_deg; trivial. rewrite mkseqSr. smt(@BasePoly). simplify.
     have : forall b, (p * polyCn 1 c).[0] * exp a 0 + b = b. rewrite expr0. rewrite polyMCnE_0.  smt(@GP.ZModE). move => g'.
     rewrite g'. rewrite dis_mul_add. smt(@GP.ZModE). smt(@GP.ZModE). rewrite dis_mul_add. smt(@GP.ZModE). smt(@GP.ZModE).
     apply eq_foldr; trivial. apply (eq_from_nth zeror). smt(@List @BasePoly). move => i ip. rewrite nth_mkseq. smt(@List).
     rewrite (nth_map zeror). smt(@List @BasePoly). rewrite (nth_map zeror). smt(@List @BasePoly). rewrite nth_mkseq.
     smt(@List @BasePoly). move => @/(\o). simplify. have : 1 + i = i + 1. smt(). move => g. rewrite g. rewrite exprS. smt().
     rewrite polyM_polyCn. smt(). smt(@R).
 qed.

     
   lemma polyM_eq p q k : BigCf.BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (k+1) =
       foldr R.(+) zeror (mkseq (fun i => p.[i] * q.[k-i]) (k+1)).
   proof.
     case (0 <= k + 1); move => h. apply foldr_mkseq_bigi_eq. smt(). move => @/bigi @/range. rewrite iota0. smt().
     rewrite BigCf.BCA.big_nil. rewrite mkseq0_le. smt(). smt().
   qed.

      
   lemma polyM_polyC p i j: 0<= j =>  (p * polyC i).[j] = p.[j] * i.
   proof.
     move => h. rewrite polyME. rewrite polyM_eq. simplify. rewrite mkseqS; trivial. simplify. rewrite foldr_rcons.
     have : p.[j] * (polyC i).[0] + zeror = zeror + p.[j] * (polyC i).[0]. smt(@GP.ZModE). move => h'. rewrite h'.
     rewrite foldr_const. smt(@GP.ZModE). smt(@GP.ZModE). rewrite foldr_id.  smt(@GP.ZModE). apply (all_nth _ zeror).
     move => s ps. simplify. rewrite nth_mkseq. smt(@List). simplify. rewrite polyCE. simplify. have : j - s <> 0.
     smt(@List). move => g. rewrite g. simplify. smt(@GP.ZModE). smt(@BasePoly @GP.ZModE). 
   qed.

 
    lemma peval_polyM_C p a i : peval (p * polyC i) a = peval p a * i.
   proof.
     rewrite peval_simp. rewrite peval_simp.  case (i = zeror); move => h. 
     (* special case *)
     rewrite h. have : deg (p * polyC zeror) + 1 = 1. smt(@BasePoly). move => h'. rewrite h'. rewrite mkseq1.
     simplify. smt(@BasePoly @GP.ZModE).
     (* General case *)
     rewrite dis_mul_add. smt(@GP.ZModE). smt(@GP.ZModE). apply eq_foldr; trivial.
     apply (eq_from_nth zeror). rewrite size_mkseq. rewrite size_map. rewrite size_mkseq.  smt(@BasePoly).
     move => j jp. rewrite nth_mkseq. smt(@List). rewrite (nth_map zeror). smt(@List @BasePoly). rewrite nth_mkseq.
     smt(@List @BasePoly). simplify. rewrite polyM_polyC. smt(). smt(@GP.ZModE).
  qed.
 
  lemma peval_polyM_polyD2 p c1 c0 a: peval (p * (polyD2 c1 c0)) a = peval p a * c1 * a + peval p a * c0.
   proof.
     case (p = poly0); move => h.
     (* stupid case *)
     rewrite h. smt(peval0 @BasePoly @GP.ZModE).
     (* second stupid case *)
     case (c1 = zeror) => h'. subst. rewrite polyD2_polyC. rewrite peval_polyM_C. smt(@R).
      (* resume *)
     rewrite !peval_simp. rewrite polyMD2_deg; trivial. 
     (* seq equal *)
     rewrite dis_mul_add.  smt(@GP.ZModE). smt(@GP.ZModE). rewrite dis_mul_add.  smt(@GP.ZModE). smt(@GP.ZModE).
     rewrite (dis_mul_add _ _ _ _ c0).  smt(@GP.ZModE). smt(@GP.ZModE). rewrite mkseqSr. smt(@BasePoly).
     rewrite (map_mkseq (fun (x : GP.exp) => x * c0)).
     rewrite (mkseqSr ((fun (x : GP.exp) => x * c0) \o fun (i : int) => p.[i] * exp a i)). smt(@BasePoly). simplify.
     have: forall (a b c d e : GP.exp), a = d => b = c + e => a + b = c + (d + e). smt(@GP.ZModE). move => g'. apply g'.
     move => @/(\o). rewrite expr0. rewrite polyMD2_0. smt(@R). have : forall (a b : GP.exp), a + b = b + a. smt(@GP.ZModE).
     move => g''. rewrite g''. rewrite foldr_add_distr_sub. smt(@GP.ZModE). smt(@GP.ZModE). smt(@GP.ZModE).
     smt(@List). rewrite size_mkseq. rewrite size_map. rewrite size_map. rewrite size_mkseq. 
     apply eq_foldr; trivial. apply (eq_from_nth zeror). smt(@List @BasePoly). move => i ip. rewrite nth_mkseq. smt(@List).
     rewrite (nth_mkseq zeror). smt(@List @BasePoly). simplify.  rewrite (nth_map zeror). smt(@List @BasePoly). 
     rewrite (nth_map zeror). smt(@List @BasePoly). move => @/(\o). simplify.  have : 1 + i = i + 1. smt(). move => g'''. 
     (* end case *)
     case (i = deg p) => h''. rewrite nth_default. smt(@List). rewrite nth_mkseq.  smt(@List @BasePoly). simplify.
     rewrite g'''. rewrite polyM_polyD2; trivial. smt(). smt(@R @BasePoly).
     (* normal case*)
     rewrite nth_mkseq.  smt(@List @BasePoly).  rewrite nth_mkseq.  smt(@List @BasePoly). simplify.
     rewrite g'''. rewrite polyM_polyD2; trivial. smt(). rewrite polyD2E. simplify. rewrite exprS. smt().
     have : forall (a b c : GP.exp), (a + b) * c = (a * c) + (b * c). smt(@R). move => k. rewrite k. rewrite g''. congr.
     smt(@R). smt(@R).
 qed.
 
  lemma peval_polyCn_prod a bs (f : GP.exp -> GP.exp) :
    peval (foldr BasePoly.( * ) poly1 (map (fun x => polyCn 1 (f x)) bs)) a = 
    foldr R.( * ) oner (map (fun x => a *x) (map f  bs)).
  proof.
    elim bs. simplify. rewrite peval_polyC. trivial. simplify. move => x l ind_hyp. rewrite IDPoly.mulrC.
    rewrite peval_polyM_polyCn. rewrite ind_hyp. smt(@R).
  qed.
  
  lemma peval_polyD2_prod a bs (f f' : GP.exp -> GP.exp) :
    peval (foldr BasePoly.( * ) poly1 (map (fun x => polyD2 (f x) (f' x)) bs)) a = 
    foldr R.( * ) oner (map (fun (x : GP.exp*GP.exp)  => a * x.`1 + x.`2 ) (map (fun x => (f x, f' x))  bs)). 
  proof.
    elim bs. simplify. rewrite peval_polyC. trivial. simplify. move => x l ind_hyp. rewrite IDPoly.mulrC.
    rewrite peval_polyM_polyD2. rewrite ind_hyp. smt(@R).
  qed.

  lemma peval_over_Xi p i a : peval p a * peval (X - polyC i) a =
      peval (p * (X - polyC i)) a.
  proof.
    have: p * (X - polyC i) = p * X - p * (polyC i). smt(@BasePoly). move => h. rewrite h.
    rewrite -peval_add. rewrite -peval_add. rewrite -peval_neg. rewrite -peval_neg.
    rewrite peval_X. rewrite peval_polyC. rewrite peval_polyM_C. rewrite peval_polyM_X. smt(@GP.ZModE).
  qed.

  lemma peval_Xi_prod js f i : peval (foldr BasePoly.( * ) poly1 (map (fun (x : GP.exp) => X - polyC (f x)) js)) i =
      foldr R.( * ) oner (map (fun (x : GP.exp) => i - (f x)) js).
  proof.
    elim js. simplify. smt(peval_polyC). move => x l ind_hyp. simplify.  rewrite -ind_hyp.
    rewrite mulpC. rewrite -peval_over_Xi. rewrite -peval_add. rewrite peval_X. rewrite -peval_neg. rewrite peval_polyC.
    smt().  
  qed.

  
  lemma polyL_cat0 x l : of_poly (polyL (x :: l)) 0  = x.
  proof.  
    smt(@BasePoly).
  qed.

  (* Movement for polynomials *)
  lemma poly_shift (a b c : poly) : c <> poly0 => c * a = c * b  <=> a = b.  
      move => g. split => h. apply (BasePoly.IDPoly.mulfI c). trivial. trivial. smt().
    qed.

   lemma poly_shift2 (a b c : poly) : c <> poly0 => a * c = b * c <=> a = b.  
      move => h. rewrite BasePoly.IDPoly.mulrC. rewrite (BasePoly.IDPoly.mulrC b c). apply poly_shift. trivial.
   qed.
   
  lemma scale_1 c phi : c=oner => c ** phi = phi.
  proof. move => h. rewrite h. apply poly_eqP. move => c0 ch. smt(@BasePoly @GP.ZModE). qed.

  lemma Xi_0 i : (X - polyC i).[0] = - i. smt(@BasePoly). qed.
  lemma Xi_1 i : (X - polyC i).[1] = oner. smt(@BasePoly). qed.
  lemma Xi_0_add i : (X + polyC i).[0] = i. rewrite polyDE. smt(@BasePoly @GP.ZModE).  qed.
  lemma Xi_1_add i : (X + polyC i).[1] = oner. smt(@BasePoly). qed.

  lemma Xi_neq_0 i : (X - polyC i) <> poly0. smt(@BasePoly). qed.

  (* Basic facts on Polys not in the standard libary which don't need division *)
  lemma poly0_mul a b : a <> poly0 => b <> poly0 => a * b <> poly0.
   smt(@BasePoly).
  qed.
    
  op euclidef (m d : sT) (qr : sT * sT) =
     m = qr.`1 * d + qr.`2
  /\ (d <> poly0 => 0 <= deg qr.`2 < deg d).
  
  op edivpoly (m d : sT) =
    if d = poly0 then (poly0, m) else choiceb (euclidef m d) (poly0, poly0)
  axiomatized by edivn_def.

  (* it would be nice to discharge this axiom *)
  axiom euclidef_true (m d : sT) : exists x, (euclidef m d) x.
      
  lemma polyRemThem_corr p d : d <> poly0 =>
    p = ((edivpoly p d).`1 * d) + (edivpoly p d).`2.
  proof.
    move => h @/edivpoly. rewrite h. simplify. have : exists x, (euclidef p d) x. apply  euclidef_true. move => h'.
    apply (choicebP _ (poly0, poly0)) in h'. smt().
  qed.

   lemma polyRemThem_adj p i :
    p - (edivpoly p (X-polyC i)).`2 = (edivpoly p (X-polyC i)).`1 * (X-polyC i).
  proof.
    smt(@BasePoly polyRemThem_corr).
  qed.

    lemma degDiv_2 m d : d <> poly0 => deg (edivpoly m d).`2 < deg d.
  proof.
    move => h. case (exists x, euclidef m d  x). elim.  move => x h'. 
    have : m =  (edivpoly m d).`1 * d +  (edivpoly m d).`2 /\ deg  (edivpoly m d).`2 < deg d. smt(choicebP).
    move => h''. smt().
    (* otherwise *)
    move => h'. have : (edivpoly m d).`2 = poly0. smt(choiceb_dfl). move => h''.
    rewrite h''. smt(@BasePoly).
  qed.
  
  lemma polyRemThem_r p i :
      polyC (peval p i) = (edivpoly p (X-polyC i)).`2.
  proof.
    have : peval (edivpoly p (X - polyC i)).`1 i * (i + -i) = zeror. smt(@R). move => h'.     
    have : peval p i = peval ((edivpoly p (X - polyC i)).`1 * (X - polyC i) + (edivpoly p (X - polyC i)).`2) i.
    smt(polyRemThem_corr Xi_neq_0). rewrite -peval_add. rewrite -peval_over_Xi. rewrite -peval_add.
    rewrite peval_X. rewrite -peval_neg. rewrite peval_polyC. move => h. rewrite h' in h. rewrite h.
    have : (edivpoly p (X - polyC i)).`2 = polyC (peval (edivpoly p (X - polyC i)).`2 i). rewrite eq_sym. apply polyC_peval.
    smt(degDiv_2 @BasePoly). move => h'''. rewrite h'''. congr.  smt(@R).
  qed. 
      
  lemma ediv_uniq (p a a' b b' d : poly) : d <> poly0 => deg b < deg d => deg b' < deg d =>
    p = a * d + b => p = a' * d + b' => a=a' /\ b=b'.
  proof.    
    move => d0 degb degb' h0 h1. have : (a - a') * d = b' -b. rewrite h0 in h1.
    have : a * d - a' * d = b' - b. smt(@BasePoly). move => h'. rewrite -h'. smt(@BasePoly).
    move => h2. smt(@BasePoly).
  qed.

  lemma ediv_uniq_1 (p a a' b b' d : poly) : d <> poly0 => deg b < deg d => deg b' < deg d =>
    p = a * d + b => p = a' * d + b' => a=a'.
  proof.    
    smt(ediv_uniq).
  qed.
  
  lemma ediv_add (p p' d : poly) :  d <> poly0 =>
    p + p' = (((edivpoly p d).`1 + (edivpoly p' d).`1)  * d) + ((edivpoly p d).`2 + (edivpoly p' d).`2).
  proof.
    move => h. have : ((edivpoly p d).`1 + (edivpoly p' d).`1) * d +((edivpoly p d).`2 + (edivpoly p' d).`2) =
   ((edivpoly p d).`1 * d + (edivpoly p d).`2) + ((edivpoly p' d).`1 * d + (edivpoly p' d).`2). smt(@BasePoly).
    move => h'. rewrite h'. rewrite -polyRemThem_corr. trivial. rewrite -polyRemThem_corr. trivial. trivial.
 qed.

 lemma ediv_add_1 (p p' d : poly) : d <> poly0 =>
   (edivpoly (p+p') d).`1 = (edivpoly p d).`1 + (edivpoly p' d).`1.
 proof.
   move => h. apply (ediv_uniq_1 (p + p') (edivpoly (p + p') d).`1 ((edivpoly p d).`1 + (edivpoly p' d).`1)
   (edivpoly (p + p') d).`2 ((edivpoly p d).`2 + (edivpoly p' d).`2) d). trivial. apply degDiv_2; trivial.
     smt(degDiv_2 @BasePoly). apply polyRemThem_corr; trivial. apply ediv_add; trivial.
  qed.
 
 lemma ediv_scale
   a (p d : poly) :  d <> poly0 =>
   a ** p = (a ** ((edivpoly p d).`1 * d)) + (a ** (edivpoly p d).`2).
 proof.
   pose p1 := (edivpoly p d).`1. pose p2 := (edivpoly p d).`2. move => h. rewrite (polyRemThem_corr p d).
   trivial. move => @/p1 @/p2. rewrite BasePoly.scalepDr. trivial. 
 qed.

  lemma ediv_scale_1 a (p d : poly) : d <> poly0 =>
    (edivpoly (a ** p) d).`1 = a ** (edivpoly p d).`1.
  proof.
    move => h. have : a ** p = (a ** ((edivpoly p d).`1 * d)) + (a ** (edivpoly p d).`2).
    apply ediv_scale; trivial.  have : a ** p = ((edivpoly (a ** p) d).`1 * d) + (edivpoly (a ** p) d).`2.
    apply polyRemThem_corr; trivial. move => h1 h2. rewrite (scalepE _ ((edivpoly p d).`1 * d)) in h2.
    rewrite eq_sym. rewrite scalepE. rewrite -eq_sym.
    apply (ediv_uniq_1 _ _ (polyC a * (edivpoly p d).`1) _ (a ** (edivpoly p d).`2) _ h _ _ h1 _).
    apply degDiv_2; trivial. smt(degDiv_2 @BasePoly). smt(@BasePoly).
  qed. 

  lemma ediv_neg (p d : poly) :  d <> poly0 =>
    - p = (edivpoly (-p) d).`1 * d + (edivpoly (-p) d).`2.
  proof.
    move => h. rewrite -polyRemThem_corr; trivial. 
  qed.
 
  lemma ediv_neg_1 (p d : poly) : d <> poly0 =>
    (edivpoly (-p) d).`1 = - (edivpoly p d).`1.
  proof.
    move => h. apply (ediv_uniq_1 (-p) _ _ (edivpoly (-p) d).`2 (- (edivpoly (p) d).`2) d); trivial.
    apply degDiv_2; trivial. smt(degN degDiv_2). apply ediv_neg. trivial.
    have : (- (edivpoly p d).`1) * d - (edivpoly p d).`2 = - ((edivpoly p d).`1 * d + (edivpoly p d).`2).
    smt(@IDPoly). move => h'. rewrite h'. smt(polyRemThem_corr).  
  qed. 
  
  lemma degDiv m d : deg (edivpoly m d).`1 <= deg m.
  proof.
    case (exists x, euclidef m d  x). move => h. case (d = poly0); move => h'. smt(@BasePoly).
    have : m =  (edivpoly m d).`1 * d +  (edivpoly m d).`2 /\ deg  (edivpoly m d).`2 < deg d. smt(choicebP). move => h''.
    elim h''. move => h'' h'''. pose q := (edivpoly m d).`1. rewrite h''. case ((edivpoly m d).`1 = poly0); move => g.
    (* case when d is greater then m *)
    rewrite IDPoly.addrC. case ((edivpoly m d).`2 = poly0); move => g'. smt(@BasePoly). rewrite degDl. rewrite g.
    smt(@BasePoly). smt(@BasePoly).
    (* otherwise *)
    rewrite degDl. rewrite degM.  trivial. trivial.
    smt(@BasePoly). smt(@BasePoly).
    move => h. have : (edivpoly m d).`1 = poly0. smt(choiceb_dfl). move => h'.
    rewrite h'. smt(@BasePoly).
qed.

lemma degDiv2 m d t : deg m <= t => deg (edivpoly m d).`1 <= t.
proof.
  smt(degDiv).
qed.

  lemma degDiv_Xi m i : deg (edivpoly m (X - polyC i)).`2 < 2.
  proof.
    have : deg (X - polyC i) = 2. smt(@BasePoly). move => h. rewrite -h. apply degDiv_2.
    smt(@BasePoly).
  qed.

  (* p/(X-i)[a] = (p[a]-p[i])/(a-i) *)
  lemma prt_eval p (i a : GP.exp) :  (-i) + a <> zeror =>
    peval (edivpoly p (X - polyC i)).`1 a = (peval p a - peval p i)/(a-i).
      move => g. have : peval (edivpoly p (X - polyC i)).`1 a * (a-i) =  (peval p a - peval p i) =>
      peval (edivpoly p (X - polyC i)).`1 a = ((peval p a - peval p i) / (a - i))%R.
      move => h. rewrite -h. rewrite -R.mulrA. rewrite R.mulrV. smt(@GP.ZModE).  smt(@GP.ZModE).
      move => h. apply h. have : (a-i) = peval (X - polyC i) a.
      rewrite -peval_add. rewrite -peval_neg.
      rewrite peval_polyC. rewrite peval_X. trivial. move => h'. rewrite h'. rewrite peval_over_Xi.
      rewrite -polyRemThem_adj. rewrite -peval_add. rewrite -polyRemThem_r. rewrite -peval_neg.
      rewrite peval_polyC. trivial.
    qed.

    
  lemma prt_eval2 phi phi' (i a b : GP.exp) : (-i) + a <> zeror =>
      peval (edivpoly phi (X - polyC i)).`1 a + b * peval (edivpoly phi' (X - polyC i)).`1 a =
      peval (edivpoly (b ** phi' + phi) (X - polyC i)).`1 a.
  proof.
    move => h. rewrite !prt_eval; trivial. rewrite -!peval_add -!peval_mul.
    have : peval phi' a * b + peval phi a - (peval phi' i * b + peval phi i) =
    b * (peval phi' a - peval phi' i) + peval phi a - peval phi i. rewrite GP.ZModE.ZModpField.opprD.
    rewrite !GP.ZModE.ZModpField.addrA. congr; trivial. rewrite GP.ZModE.ZModpField.addrC.
    rewrite GP.ZModE.ZModpField.addrA.
    pose x := peval phi' a. pose y := peval phi' i. smt(@GP.ZModE).

    move => g. rewrite g. rewrite !GP.ZModE.ZModpField.mulrDl. rewrite -GP.ZModE.ZModpField.addrA.
    rewrite (GP.ZModE.ZModpField.addrC). rewrite -GP.ZModE.ZModpField.mulrDl. smt(@GP.ZModE). 
qed.


lemma Xi_eval_inv i : GP.ZModE.inv (peval (X - polyC i) i) = peval (X - polyC i) i.
proof.
  rewrite !Xi_eval. smt(@GP.ZModE).
qed.

(* the number of roots is bounded by the degree - 1 *)
(* Note that in easycrypt libary x has degree 2 and x^2 has degree 3 *)
axiom roots_bounded_by_degree p rs : p <> poly0 => uniq rs => all (BasePoly.root p) rs => size rs <= deg p -1.
op findroots : poly -> GP.exp list.
axiom findroots_corr p rs : rs = findroots p => uniq rs /\  all (BasePoly.root p) rs.
axiom findroots_size p : 1 < deg p => size (findroots p) = deg p -1.

lemma root_in_findroots p a : 1 < deg p => BasePoly.root p a => a \in (findroots p).
proof.
  move => h h'. have : uniq (findroots p) /\ all (BasePoly.root p) (findroots p). apply findroots_corr; trivial.
  move => g. have : (size (findroots p) = deg p -1). apply findroots_size; trivial. move => g'.
  case (a \in findroots p) => h''. trivial. have : size (a :: findroots p) <= deg p -1. apply roots_bounded_by_degree.
  smt(@BasePoly). smt(@List). smt(@List). smt().
qed.

(* Some easier to use variants of the deg lemmas *)

lemma degD_sim p q a : deg p <= a => deg q <= a => deg (p + q) <= a.
proof.
  move => h0 h1. smt(degD).   
qed.
  
lemma degZ_le_gen c p a : deg p <= a => deg (c ** p) <= a.
proof.
  move => h0. smt(degZ_le).
qed.

(* Some lemmas for polynomial  *)

op lb (j : GP.exp)(js: GP.exp list) : poly = foldr polyM poly1 (map (fun (x : GP.exp) => (polyD2 (invr (j-x)) ((-x)/(j-x)))) js).

lemma deg_lb j js : deg (lb j js) <= size js + 1.
 proof.
 move => @/lb. elim js. simplify. smt(@BasePoly). move => x l ind_hyp. simplify.
 have : deg (polyD2 (invr (j - x)) ((-x) / (j - x))) <= 2. apply deg_leq_polyD2. smt(@BasePoly).
qed.

lemma lb_1 js i : 0 <= i < size js => uniq js => peval (lb (nth zeror js i) (rem (nth zeror js i) js)) (nth zeror js i) = oner.
proof.
  move => h h' @/lb. rewrite peval_polyD2_prod.  apply foldr_id; trivial. smt(@R).  apply (all_nthP _ _ oner). move => i0 hi0.
  rewrite !size_map in hi0. rewrite size_rem in hi0. smt(@List). rewrite (nth_map (oner,oner)). smt(@List).
  rewrite (nth_map zeror). smt(@List). simplify. have : (nth zeror js i - nth zeror (rem (nth zeror js i) js) i0) <> zeror.
  have : forall (a b : GP.exp), a <> b => a - b <> zeror. smt(@GP.ZModE.ZModpField). move => g. apply g. smt(@List).
   smt(@GP.ZModE.ZModpField).
qed.

lemma lb_0 js (i i0 : int) : i<> i0 => 0 <= i0 < size js => 0 <= i < size js => uniq js => 
    peval (lb (nth zeror js i0) (rem (nth zeror js i0) js)) (nth zeror js i) = zeror.
proof.
  move => h h' h'' h'''. rewrite peval_polyD2_prod. apply foldr_ann_in. smt(@R). smt(@R). apply (nthP zeror).
  exists (if i < index (nth zeror js i0) js then i else i -1).
  have : index (nth zeror js i0) js <> i. smt(@List). move => g.
  (* size *)
  split. rewrite !size_map. rewrite size_rem. smt(@List). smt(@List). 
  (* eq *)
  rewrite (nth_map (zeror, zeror)). smt(@List). rewrite (nth_map (zeror)). smt(@List). rewrite rem_nth. smt(@List).
  simplify. case(i < index (nth zeror js i0) js) => g'. rewrite g'.  simplify. smt(@R).
  have : ! i - 1 < index (nth zeror js i0) js. smt(@List).  move => g''. rewrite g''. smt(@R).
qed.

op lbs (js: GP.exp list) : poly list  = mkseq (fun i => lb (nth zeror js i) (rem (nth zeror js i)  js)) (size js).

op interpolate (js: GP.exp list)(phiis : GP.exp list) : poly = foldr polyD poly0
                              (map (fun (x : GP.exp*poly) => x.`1 ** x.`2) (zip phiis (lbs js))).

lemma interpolate_deg js phiis: size js = size phiis =>  deg (interpolate js phiis) <= size js.
  move => h @/interpolate.
  have : forall a, all (fun x => deg x <= size js) a => deg (foldr BasePoly.(+) poly0 a) <= size js.
  move => a. elim a. smt(@BasePoly). smt(@BasePoly). move => g. apply g. apply (all_nth _ poly0). move => i hi.  
  rewrite (nth_map (zeror, poly0)). smt(@List). simplify. rewrite nth_zip. smt(@List). simplify. apply degZ_le_gen.
  rewrite nth_mkseq. smt(@List). simplify. smt(deg_lb @List). 
 qed.
  
(* prove interpolation *)                              
lemma interpolate_int js phis : size js = size phis => uniq js => map (fun x => peval (interpolate js phis) x) js = phis.
proof.
  move => h uniq. apply (eq_from_nth zeror). rewrite size_map; trivial. rewrite size_map; trivial.  move => i hi.
  rewrite (nth_map zeror). trivial. simplify. move => @/interpolate. rewrite peval_sum. 
  have : (map (fun (phi : poly) => peval phi (nth zeror js i)) (map (fun (x : GP.exp * poly) => x.`1 ** x.`2) (zip phis (lbs js))))
= mkseq (fun i0 => peval (nth zeror phis i0 ** (lb (nth zeror js i0) (rem (nth zeror js i0) js))) (nth zeror js i)) (size js).
  (* rewrite as mkseq *)
  apply (eq_from_nth zeror).  smt(@List). move => i0 hi0. rewrite (nth_map poly0). smt(@List). rewrite (nth_map (zeror, poly0)).
  smt(@List). rewrite nth_mkseq. smt(@List). smt(@List). 
  (* resume main *)
  move=> g. rewrite g. rewrite (foldr_id_nth_mkseq _ _ _  i); trivial. smt(@R). smt(@R). smt(@R).
  (* all basis except i have roots at *)
  apply (all_nthP _ _ zeror). move => i0 hi0. rewrite size_mkseq in hi0. rewrite nth_mkseq. smt(). simplify.
  rewrite -peval_mul. rewrite lb_0; trivial. smt(). smt(@List). smt(@R).
  apply (all_nthP _ _ zeror). move => i0 hi0. rewrite size_mkseq in hi0. rewrite nth_mkseq. smt(). simplify.
  rewrite -peval_mul. rewrite lb_0; trivial. smt(). smt(@List). smt(@R). 
  (* 1 everywhere else *)
  simplify. rewrite -peval_mul. rewrite lb_1; trivial. smt(@R).
qed.

(* prove uniq *) 
lemma interpolate_uniq js phis pi pi' : deg pi <= size js => deg pi' <= size js => uniq js =>
    phis = map (peval pi) js =>  phis = map (peval pi') js => pi = pi'.
proof.
  move => deg1 deg2 uniq_js eval1 eval2. case(pi = pi') => h. trivial.
  have: size js <= deg (pi-pi') - 1. apply roots_bounded_by_degree; trivial. smt(@IDPoly).
  apply (all_nth _ zeror). move => i hi @/root. simplify. rewrite -peval_add. rewrite -peval_neg. smt(@R @List).
  smt(@BasePoly).
qed.

(* prove correctness (inter. + uniq *)
lemma interpolate_corr js phis phi : deg phi <= size js => size js = size phis => uniq js =>
    phis = map (fun x => peval phi x) js <=> interpolate js phis = phi.  
proof. 
  move => deg_phi h_size h_uniq. split => h.
  (* direction 1*)
  have : phis = map (peval (interpolate js phis)) js. smt(interpolate_int). move => g.
  apply (interpolate_uniq js phis); trivial. apply interpolate_deg; trivial. 
  (* direction 2*) rewrite -h. rewrite eq_sym. apply interpolate_int; trivial.
qed.
 
lemma interpolate_nth js phiis i : size js = size phiis =>
    (interpolate js phiis).[i] = foldr R.( + ) zeror
    (map (fun (x : GP.exp*GP.exp) => x.`1 * (lb x.`2 (rem x.`2  js)).[i]) (zip phiis js)).
proof.
  move => h @/interpolate. rewrite poly_sum_nth. congr.  apply (eq_from_nth zeror). smt(@List).
  move => i0 hi0. rewrite (nth_map poly0). smt(@List). rewrite (nth_map (zeror,zeror)). smt(@List).
  rewrite (nth_map (zeror,poly0)). smt(@List). simplify. rewrite nth_zip. smt(@List).
   rewrite nth_zip. smt(@List). simplify. rewrite nth_mkseq. smt(@List). simplify. smt(@BasePoly).
qed.

(* Theis should both be replaced with lagrange interpolation *)
op pairwise_add (s t : GB.group list) =
  with s = x :: s', t = y :: t' => (GB.( * )x y) :: pairwise_add s' t'
  with s = _ :: _ , t = []      => []
  with s = []     , t = _ :: _  => []
  with s = []     , t = []      => [].

lemma pairwise_add_size s t : size s = size t => size (pairwise_add s t) = size s.
proof.
  elim s. elim t. trivial. smt(@List). elim t. smt(@List). smt().
qed.

lemma pairwise_sum_size l j : 0 <= j => all (fun x => size x = j) l =>
    size (foldr pairwise_add (mkseq (fun (_ : int) => GB.e) j) l) = j.
 proof.
  move => h. elim l. simplify. smt(@List). move => x l ind_hyp hsize. simplify. rewrite pairwise_add_size.
  rewrite ind_hyp. smt(@List). smt(@List). smt(@List).
qed.
 
lemma pairwise_add_nth_sub : forall j, 0 <= j => forall x y i, size x = j => size y = j =>
    nth GB.e (pairwise_add x y) i = GB.( * ) (nth GB.e x i) (nth GB.e y i).
proof.
  apply intind. smt(@List @GB). simplify. move => i0 h int_ind. move => x y. elim x. smt(@List). elim y. smt(@List).
  move => x l  g x0 l0 g'. clear g g'. move => i g g'. simplify. case(i =0) => g''. trivial. apply int_ind. smt(@List).
  smt(@List).
qed.

lemma pairwise_add_nth x y i : size x = size y => nth GB.e (pairwise_add x y) i = GB.( * ) (nth GB.e x i) (nth GB.e y i).
proof.
  move => h. apply (pairwise_add_nth_sub (size x)); trivial. smt(@List).
qed.

lemma pairwise_sum_nth j l i : all (fun x => size x = j) l =>
    nth GB.e (foldr pairwise_add (mkseq (fun (_ : int) => GB.e) j) l) i =
    foldr GB.( * ) GB.e (map (fun x=> nth GB.e x i) l).
proof.
  elim l. simplify. smt(@List). move => x l ind_hyp h. simplify. rewrite -ind_hyp. smt(@List).
  rewrite pairwise_add_nth. rewrite pairwise_sum_size. trivial. smt(@List). smt(@List). smt(@List). trivial.
qed.

op interpolate_exp (js : GP.exp list)(phiis : GB.group list) : GB.group list =
foldr pairwise_add (mkseq (fun (x :int) => GB.e) (size js))
(map (fun (x : GB.group*poly) => mkseq (fun i => GB.( ^ ) x.`1 (GP.ZModE.asint x.`2.[i])) (size js)) (zip phiis (lbs js))).

lemma interpolate_exp_size js phiis : size (interpolate_exp js phiis) = size js.
proof.
  move => @/interpolate_exp. have : forall a b, 0 <= b => all (fun x => size x = b) a =>
  size (foldr pairwise_add (mkseq (fun (_ : int) => GB.e) b) a) = b. move => a. elim a. simplify. move => b.
  rewrite size_mkseq. smt(). move => x l ind_hyp b hb h. simplify. rewrite pairwise_add_size. rewrite ind_hyp; trivial.
  smt(@List). smt(@List). smt(@List).
  move => h. apply h. smt(@List). apply (all_nth _ []). move => i hi. rewrite (nth_map (GB.g, poly0)). smt(@List). simplify.
  smt(@List). 
qed.
    
op peval_exp g_phi a =  List.foldr GB.( * ) GB.e
      (mkseq (fun (i : int) => GB.( ^ )(nth GB.e g_phi i)
          (GP.ZModE.asint (GP.ZModE.exp a i))) (size g_phi)).

lemma inter_eval js phiis a : size phiis = size js =>
  peval_exp (interpolate_exp js (map (fun x1 => GB.(^) GB.g (GP.ZModE.asint x1)) phiis)) a =
    GB.( ^ ) GB.g (GP.ZModE.asint (peval (interpolate js phiis) a)).
proof.
  move => h @/peval_exp. rewrite interpolate_exp_size. rewrite (peval_simp_gen _  _ (size js)). apply interpolate_deg; trivial.
  rewrite h. trivial. rewrite -(prod_sum_eq _ zeror). move => @/interpolate_exp. congr. apply (eq_from_nth GB.e).
  smt(@List). move => i hi. rewrite size_mkseq in hi. rewrite !nth_mkseq. smt(). smt(@List). simplify. 
  rewrite (pairwise_sum_nth (size js) _ i).  apply (all_nth _ []). move => i0 hi0. simplify. rewrite (nth_map (GB.e,poly0)).
  smt(@List). smt(@List). rewrite nth_mkseq. smt(). simplify. rewrite -exp_GB_asint_mul. rewrite GB.expM. congr.
  (* go it to the point where neec only show that the coefficents are equal *)
  rewrite interpolate_nth. rewrite h. trivial. rewrite -(prod_sum_eq _ zeror). congr. apply (eq_from_nth GB.e).
  smt(@List). move => i0 hi0. rewrite (nth_map []). smt(@List). rewrite nth_mkseq. smt(@List). simplify.
  rewrite (nth_map (zeror,zeror)). smt(@List). rewrite (nth_map (GB.e,poly0)). smt(@List). simplify.
  rewrite nth_mkseq. smt(@List). simplify. rewrite nth_zip. smt(@List). simplify. rewrite (nth_map zeror). smt(@List).
  simplify. rewrite -GB.expM. rewrite exp_GB_asint_mul. congr. congr. rewrite nth_zip. smt(@List). simplify.
  rewrite nth_mkseq. smt(@List). trivial. trivial.
qed.

lemma interpolate_corr2 js phiis : uniq js => size js = size phiis => map (fun x => peval (interpolate js phiis) x) js = phiis.
    move => h h'. pose phi := interpolate js phiis. rewrite eq_sym. apply interpolate_corr; trivial.
    apply interpolate_deg; trivial.
qed.   

lemma interpolate_corr2_head j js phi phis :  uniq (j :: js) => size js = size phis =>
    peval (interpolate (j :: js) (phi :: phis)) j = phi.
    move => h h'. have : map (peval (interpolate (j :: js) (phi :: phis))) (j :: js) =  (phi :: phis).
    apply interpolate_corr2; trivial. smt(@List). simplify.  move => g. smt().
qed.
  
lemma interpolate_corr2_tail j js phi phis :  uniq (j :: js) => size js = size phis =>
    map (fun x => peval (interpolate (j :: js) (phi :: phis)) x) js = phis.
    move => h h'. have : map (peval (interpolate (j :: js) (phi :: phis))) (j :: js) =  (phi :: phis).
    apply interpolate_corr2; trivial. smt(@List). simplify.  move => g. smt().
qed.

lemma interpolate_corr2_nth js phis j :  uniq js => size js = size phis =>0 <= j && j < size js =>
    peval (interpolate js phis) (nth GP.ZModE.zero js j) = nth GP.ZModE.zero phis j.
proof.
  move => g g' h. have : map (fun x => peval (interpolate js phis) x) js = phis. apply interpolate_corr2; trivial. move => h'.
  pose phi :=  (interpolate js phis). rewrite -h'. rewrite (nth_map GP.ZModE.zero).  trivial. simplify.  trivial.
qed.

lemma interpolate_corr2_nth_tail j js phi phis i :  uniq (j :: js) => size js = size phis => 0 <= i && i < size js =>
    peval (interpolate (j :: js) (phi :: phis)) (nth GP.ZModE.zero js i) = nth GP.ZModE.zero phis i.
proof.
   move => g g' h. have : map (fun x => peval (interpolate (j :: js) (phi :: phis)) x) js = phis.
  apply interpolate_corr2_tail; trivial. smt(@List).
qed.

lemma inter_inter j j' js js' x phii : size js = size phii => size js' = size phii => uniq (j :: js) =>
    interpolate (j :: js) (map (peval (interpolate (j' :: js') (x :: phii))) (j :: js)) =
    interpolate (j' :: js') (x :: phii).
proof.
  move => h0 h1 h2. apply interpolate_corr; trivial. smt(interpolate_deg). smt(@List).
qed.

lemma inter_inter_tail a x js js'0 phi : size js'0 = size phi => size js = size phi =>
    uniq (a :: js) => uniq (a :: js'0) =>
    interpolate (a :: js) (x :: map (peval (interpolate (a :: js'0) (x :: phi))) js) =
    interpolate (a :: js'0) (x :: phi).
 proof.
   move => h0 h1 h2 h3. apply interpolate_corr; trivial. smt(interpolate_deg). smt(@List). simplify. smt(interpolate_corr2_head).
 qed.

(* randomly sampling the coefficents of a polynomial or sampling eval values is the same *)
lemma interpolate_prob (phiis : GP.exp * GP.exp list) js t : uniq js => size js = t => size phiis.`2 = t -1 =>
  mu1 (FD.dt `*` dlist FD.dt (t - 1)) phiis =
mu1 (dpoly t FD.dt)
    (interpolate js (phiis.`1 :: phiis.`2)).    
proof.
  move => h h' h''. rewrite AddDistr.dlistS_join; trivial. rewrite (AddDistr.dlist_mu1 _ _ GT.order); trivial.
  smt(@List). smt(@FD). rewrite (in_dmap1E_can _ _ (fun pi => mkseq (fun i => pi.[i]) t)). move => @/polyL.
  apply poly_eqP. move => c hc. rewrite coeffE. smt(@BasePoly). move =>  @/prepolyL. simplify.
  case (c < deg (interpolate js (phiis.`1 :: phiis.`2))). move => g. rewrite nth_mkseq. smt(interpolate_deg). trivial.
  smt(@List @BasePoly). move => y hy heq. simplify. rewrite -heq. apply (eq_from_nth zeror). smt(@List @DList).
  move => i hi. rewrite nth_mkseq. smt(@List @DList). smt(@List @BasePoly).
  rewrite (AddDistr.dlist_mu1  _ _ GT.order). smt(@List). smt(@FD). trivial.
qed.

(* You can't do better then guessing an evaluation if the polynomial is random up to deg-1 indepedent points *)
axiom interpolate_prob2 phii i (v2 : GP.exp list) v3 : !(i \in v2) => size v2 = t-1 =>
  mu FD.dt (fun (x : GP.exp) => mu FD.dt (fun (x0 : GP.exp) =>
    phii = peval (interpolate (x :: v2) (x0 :: v3)) i) = inv GB.order%r) = 1%r.

(* this should follow from interpolate_prob *)
axiom interpolate_prob3 phi j js : mu1 (dpoly Bl.t FD.dt) phi =
mu1 (dlet FD.dt (fun x0 => dmap (dlist FD.dt (Bl.t - 1))
  (fun (phiis'0 : GP.exp list) => (x0, phiis'0)))) (peval phi j, map (peval phi) js).


axiom  interpolate_prob2_dcond phii i (v2 : GP.exp list) v3 : !(i \in v2) => size v2 = t-1 =>
  mu (dcond Bl.FD.dt (fun (x : Bl.GP.exp) => ! (x \in v2)))
  (fun (x : GP.exp) => mu Bl.FD.dt (fun (x0 : GP.exp) =>
  phii = peval (interpolate (x :: v2) (x0 :: v3)) i) = inv Bl.GB.order%r) = 1%r.

lemma interpolate_in_dpoly js phis t : size js = t => size phis = t =>
    interpolate js phis \in dpoly t FD.dt.
proof.
move => h0 h1. rewrite supp_dpoly. smt(@List). split. rewrite -h0. apply interpolate_deg; trivial. smt(). smt(@Poly @FD).
qed.

(* factor find - Given a non-zero polynomial with a root at i *)
(* and a Tsdh instance with secrect i returns i *)
op factorFind (p : poly)(ga : Bl.GB.group list): GP.exp =
  nth zeror (findroots p) (find (fun x=> ga = Bl.mkKey x) (findroots p)).

lemma factorFindCorr p p' a : p <> p' =>
  peval p a = peval p' a =>
   factorFind (p - p') (mkKey a) = a.
proof.
  move => h h'. case (deg (p-p') = 1) => g. have : exists a, (p-p') = polyC a. smt(@BasePoly). move => a0. elim a0.
  move => a0 g'. have : a0 <> zeror. smt(@BasePoly). move => h''. have : peval (p - p') a = zeror.
  rewrite -peval_add -peval_neg. smt(@GP.ZModE). move => g''. rewrite g' in g''. rewrite peval_polyC in g''. trivial.
  have : a \in (findroots (p-p')). apply root_in_findroots. smt(@BasePoly). rewrite -peval_add. rewrite -peval_neg.
  smt(@GP.ZModE). move => g' @/factorFind. pose pre := (fun (x : GP.ZModE.exp) => mkKey a = mkKey x).
  have : pre (nth zeror (findroots (p - p')) (find pre (findroots (p - p')))). apply nth_find. apply hasP.
  exists a. trivial. move => h''. apply mkKeyBij. smt().
qed.

end AddPoly.



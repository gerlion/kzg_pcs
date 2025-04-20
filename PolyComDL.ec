(* Constant-Size Commitments to Polynomials and Their Applications - PolyComDl *)

require import AllCore PolyCom Bilinear List IntDiv Ring Bigalg AddList AddPoly Distr DList DProd AddDistr.
require import FelTactic.

clone Bilinear.Bl as Bl.

clone AddPoly as PolyHelp.

import PolyHelp.
import BasePoly.
import Bl.GP.ZModE.

clone export PolynomialCommitment as PolyComDL with
  type ck <- Bl.GB.group list,
  type witness <- Bl.GB.group,
  type commitment <- Bl.GB.group, 
  type openingkey <- unit,
  type coeff <- Bl.GP.exp,
  op t <- Bl.t,
  axiom t_valid <- Bl.t_valid,
  theory IDCoeff <- R,
  theory BasePoly <- BasePoly,
  op coeff_sample = Bl.FD.dt.


abbrev ( ^ ) = Bl.GB.( ^ ).

  lemma prod_sum_eq a m:
  foldr Bl.GB.( * ) Bl.GB.e (mkseq (fun (i : int) => Bl.GB.g ^ asint (nth a m i)) (size m)) =
      Bl.GB.g ^ asint (foldr Bl.GP.ZModE.( + ) Bl.GP.ZModE.zero m).
  proof.
    elim m. simplify. rewrite mkseq0. simplify. rewrite Bl.exp0_cus. trivial.
    (* inductive case *)
    move => x l h. simplify. have : Bl.GB.g ^ (asint (Bl.GP.ZModE.( + ) x
      (foldr Bl.GP.ZModE.(+) Bl.GP.ZModE.zero l))) = Bl.GB.( * ) (Bl.GB.g ^ (asint x))
  (Bl.GB.g ^ (asint (foldr Bl.GP.ZModE.(+) Bl.GP.ZModE.zero l))). rewrite -Bl.GB.expD.
    rewrite Bl.GP.ZModE.addE. rewrite -Bl.order_eq. apply Bl.GB.expg_modz.
    move => h'. rewrite h'. rewrite -h. rewrite mkseq_add. smt(). smt(@List). rewrite List.foldr_cat.
    rewrite mkseq1. simplify. simplify. have : forall a b c,
    b = c => Bl.GB.( * ) a b = Bl.GB.( * ) a c. move => a0 b c h''. smt(). move => h''. apply h''.
    apply eq_foldr; trivial. apply (eq_from_nth Bl.GB.g). smt(@List). move => i g.
    rewrite size_mkseq in g. rewrite nth_mkseq. smt(). rewrite nth_mkseq. smt(). simplify.
    smt().
  qed.

  (* Define the key algortihms and related lemmas *)  
  op prodEx = fun x m => List.foldr Bl.GB.( * ) Bl.GB.e
      (mkseq (fun (i : int) => Bl.GB.( ^ )(nth Bl.GB.g x i)
          (asint m.[i])) (size x + 1)).

  (* We first want to prove we can rephrase the combination of mkKey and prodEx in
            a way more favorable to induction *)
  lemma mkKey_ga a : nth Bl.GB.g (Bl.mkKey a) 1 = Bl.GB.g ^ (asint a).
      rewrite nth_mkseq. smt(Bl.t_valid). simplify. smt(@Bl.GP.ZModE).
  qed.
      
  lemma prodExSimp a m : size m <= Bl.t => prodEx (Bl.mkKey a) (polyL m) =
    List.foldr Bl.GB.( * ) Bl.GB.e (mkseq (fun (i : int) =>
      Bl.GB.( ^ )(nth Bl.GB.g (mkseq (fun (i:int) =>  Bl.GB.g^(asint
                  (exp a i))) (Bl.t+1)) i)
          (asint (polyL m).[i])) (size m + 1)).
  proof.
    move => h @/prodEx @/mkKey. apply foldr_eq_partR. smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB).
    rewrite !size_mkseq. smt().
    (* Equal *) rewrite !size_mkseq. rewrite take_mkseq. smt().
    have : (max 0 (size m + 1)) = size m + 1. smt(@List). move => h'. rewrite h'. apply eq_mkseq.
    move => x. simplify. trivial.
    (* Null *) rewrite !size_mkseq. rewrite (all_nth _ Bl.GB.g). move => i h'.
    simplify. rewrite nth_drop. smt(@List). smt(@List).
    rewrite nth_mkseq. split. smt(). rewrite size_drop in h'.
    smt(@List). rewrite size_mkseq in h'. move => h''. smt().
    simplify. have : (polyL m).[max 0 (size m + 1) + i] = Bl.GP.ZModE.zero. have : deg (polyL m) <= size m. apply degL_le.
    move => g. apply gedeg_coeff. smt(@BasePoly). move => h''. rewrite h''. rewrite Bl.exp0_cus. trivial.
   qed.
   
   lemma comPolEvalSub (a : exp) m : 
    foldr Bl.GB.( * ) Bl.GB.e (mkseq (fun (i : int) =>
        Bl.GB.g ^ (asint (exp a i)) ^
        (asint (polyL m).[i]))
     (size m + 1)) =
    Bl.GB.g ^ (asint (peval (polyL m) a)).
  proof.
    rewrite PolyHelp.peval_simp. rewrite -(prod_sum_eq Bl.GP.ZModE.zero _). rewrite size_mkseq.
    apply foldr_eq_partR. smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). rewrite !size_mkseq. smt(degL_le).
    (* Show the first bit is equal *)
    rewrite size_mkseq. apply (eq_from_nth Bl.GB.g). rewrite !size_mkseq. rewrite size_take.
    smt(@BasePoly). rewrite size_mkseq. smt(degL_le). move => i h. rewrite nth_mkseq. rewrite size_mkseq in h. smt(@BasePoly).
    rewrite nth_take. smt(@BasePoly @List). smt(@BasePoly @List). rewrite nth_mkseq. rewrite size_mkseq in h.
    smt(degL_le). simplify. rewrite nth_mkseq. rewrite size_mkseq in h.
    smt(@BasePoly). simplify.
    rewrite -Bl.GB.expM. rewrite Bl.GP.ZModE.mulE. rewrite -Bl.order_eq. rewrite Bl.GB.expg_modz.
    rewrite mulrC. trivial.
    (* Show the trail is nothing *)
    rewrite size_mkseq. rewrite (all_nth _ Bl.GB.e). move => i h. simplify. rewrite nth_drop.
    smt(). smt(). rewrite nth_mkseq. rewrite size_drop in h. smt(@List).    rewrite size_mkseq in h.  smt(@BasePoly). simplify.
    have : forall a b, b = 0 => a^b = Bl.GB.e. smt(@Bl.GB). move => h''.  apply h''.
    rewrite -Bl.GP.ZModE.zeroE. apply Bl.GP.ZModE.asint_eq. apply gedeg_coeff. smt(degL_le).
  qed. 
        
  lemma comPolEval a  m : deg m <= Bl.t =>
      prodEx (Bl.mkKey a) m = Bl.GB.g ^ (asint (peval m a)).
  proof.    
    move => h. case : (surj_polyL m Bl.t h). move => s h'. elim h'; move => h' h''.
    rewrite h''. rewrite prodExSimp. smt(). rewrite (mkseq_nth_mkseq Bl.GB.g Bl.GB.g). smt(@List).
    smt(@List). simplify.  apply comPolEvalSub.
  qed.
      
  (* Now we are ready to define the main commitment scheme *)
  
  (* PK = g, g^α, . . . , g^α^t *)
  module PolyComDLScheme : PC_Scheme = {
    proc setup() : Bl.GB.group list = {
      var a : Bl.GP.exp;
      var pk : Bl.GB.group list;

      a <$ Bl.FD.dt;
      pk <- Bl.mkKey a;
      
      return pk;
    }
    
    (* c = Prod_(j=0)^t x_j^(phi_j) *)
   proc commit(x: Bl.GB.group list, m: poly) : Bl.GB.group * unit  = {
      return (prodEx x m, tt);
    }
    
    (* Checks the provided polynomials marches and returns it else zero polynomial *)
    proc open(x: Bl.GB.group list, c: Bl.GB.group, m: poly, d: unit) : poly = {
      var c';

        c' <- prodEx x m;
      return (if(c = c') then m else poly0);
    }
    
    (* Checks polynomial matches commit *)
    proc verifypoly(x: Bl.GB.group list, c: Bl.GB.group, m: poly, d: unit) : bool = {
      var c';
      c' <- prodEx x m;
      return (c=c' /\ deg m <= Bl.t);
    }

    (* Sample the polnomial at the point and create the witness *)
    proc createwitness(x: Bl.GB.group list, m: poly, i: Bl.GP.exp, d: unit) :
        Bl.GP.exp * Bl.GB.group = {
      var w;
      var phi : Bl.GP.exp;
        var psi;
      
      phi <- peval m i;
      
      (* φ(x)−φ(i) / (x−i), this is supposed to be quotient of φ(x) divided by (x-i) *)
      psi <-  (edivpoly m (X-polyC i)).`1;
      
      (* wi = g^ψi(α) *)
      w <-  prodEx x psi;
      
      return (phi, w);
    }
    
    (* (C, g) ?= e(w_i, g^α/g^i)e(g, g)^φ(i) *)
    proc verifyeval(x: Bl.GB.group list, c: Bl.GB.group, i: Bl.GP.exp, phii: Bl.GP.exp, w: Bl.GB.group) :
    bool = {
      var r, r';
        r <- Bl.e w (Bl.GB.( / ) (nth Bl.GB.g x 1) (Bl.GB.g^(Bl.GP.ZModE.asint i)));
      r' <-  Bl.GT.(^) Bl.GT.g (asint phii);
      return Bl.e c Bl.GB.g = Bl.GT.( * ) r r';
    }
  }.
  
  lemma PolyComDLScheme_Correctness : (* This always holds *)
  hoare[Correctness(PolyComDLScheme).main : true ==> res].
  proof.
    proc. inline *. wp. rnd.  auto. progress. case (Bl.t{hr} < (deg p{hr})). smt(). move => h. simplify.
    split. smt(). rewrite comPolEval. smt(). rewrite comPolEval. 
    (* Need to prove the degree was ok *)
    apply (lez_trans (deg p{hr})). apply degDiv. smt().
    (* Now we need to combine the exponets *)
    simplify. rewrite Bl.e_pow1. rewrite Bl.e_g_g. rewrite mkKey_ga.
    rewrite -Bl.GB.expB. rewrite Bl.e_pow. rewrite Bl.e_g_g. rewrite -Bl.GT.expD.
    (* Now just need to follow the argumentation int0 the exp *)
    rewrite !Bl.exp_gt_eq. rewrite !Bl.exp_GT_asint_add_r. rewrite !inzmodM !asintK. apply Bl.GP.pow_bij.
    (* concluding argument *)
    rewrite (polyRemThem_corr p{hr} (X - polyC i{hr})). apply Xi_neq_0. rewrite -peval_add.
    rewrite -(polyRemThem_corr p{hr} (X - polyC i{hr})). apply Xi_neq_0. rewrite -polyRemThem_r.
    rewrite peval_polyC. rewrite -peval_over_Xi. rewrite -peval_add. rewrite peval_X. rewrite -peval_neg. rewrite peval_polyC.
    pose crap := peval (edivpoly p{hr} (X - polyC i{hr})).`1 a . have : crap * (a  + - i{hr}) = crap * a - crap * i{hr}.
    rewrite ZModpField.mulrC. rewrite ZModpField.mulrDl.
    smt(@ZModpField). move => g.  simplify. smt(@Bl.GP.ZModE). 
qed.

   lemma not_inv (x : exp) : one - x <> - x.
       have : forall (a b c : exp), a <> c + b => a - b <> c.
       smt(@Bl.GP.ZModE). move => h. apply h. smt(@Bl.GP.ZModE).
   qed.
       
  module Adv (Adv : AdvPB) : Bl.TsdhAdv = {
    proc comp(h : Bl.GB.group list) : exp * Bl.GB.group  = {
      var c, phi, phi', d, d';
      (c, phi, phi', d, d') <@ Adv.forge(h);
      return (one - factorFind (phi - phi') h, Bl.GB.g);
    }
  }.

  lemma PolyComDLScheme_PolynomialBinding (A <: AdvPB) &m  :
        Pr[PolynomialBinding(PolyComDLScheme, A).main() @ &m : res] <=
        Pr[Bl.Tsdh(Adv(A)).main() @ &m :res].
  proof.
    byequiv. proc. inline *. auto. call (_ : true). auto. progress.
    (* main - not invese *)
    rewrite H1 in H3. have : peval result_R.`2 aL = peval result_R.`3 aL.
    apply Bl.GP.pow_bij. apply Bl.exp_GB_can. rewrite -!comPolEval; trivial. move => h. rewrite factorFindCorr. trivial.
    trivial. apply not_inv.
    rewrite H1 in H3. rewrite factorFindCorr. trivial.
    have : peval result_R.`2 aL = peval result_R.`3 aL.
    apply Bl.GP.pow_bij. apply Bl.exp_GB_can. rewrite -!comPolEval; trivial. move => h'. trivial. trivial.
    have : aL + (one - aL) = one.
    smt(@Bl.GP.ZModE.ZModpField). move => g. rewrite g.
    smt(@Bl.GB @Bl.GP.ZModE). smt(). smt().
qed.

(* EvaluationBinding *)
module Adv2 (Adv : AdvEB) : Bl.TsdhAdv = {
  proc comp(ga : Bl.GB.group list) : exp * Bl.GB.group = {
      var c, w, w' : Bl.GB.group;
      var phi, phi', i : exp;
      (c, i, phi, w, phi', w') <@ Adv.forge(ga);
        return (if (Bl.GB.g^(asint i) = nth Bl.GB.g ga 1) then
        (one - i, Bl.GB.g)
        else
        (-i,(Bl.GB.(/)w w')^(asint (one/(phi' -phi)))));
    }
  }.

lemma PolyComDLScheme_EvaluationBinding (A <: AdvEB) &m :
    Pr[EvaluationBinding(PolyComDLScheme, A).main() @ &m : res] <=
    Pr[Bl.Tsdh(Adv2(A)).main() @ &m : res].
proof.
  byequiv. proc. inline*. auto. call(:true). auto. progress.
 
  case (result_R.`2 = aL); move => h. 
  (* a = i *)
  rewrite h. rewrite (nth_mkseq). smt(@List Bl.t_valid). simplify.  have : exp aL 1 = aL. smt(@Bl.GP.ZModE).
  move => h'. rewrite h'. simplify. apply not_inv.
  (* a <> i *)
  rewrite (nth_mkseq). smt(@List Bl.t_valid). simplify.  have : exp aL 1 = aL. smt(@Bl.GP.ZModE).
  move => h'. rewrite h'. have : Bl.GB.g ^ asint result_R.`2 <>
  Bl.GB.g ^ asint aL. apply (contraNneq false). move => h''. apply h.
  rewrite Bl.exp_GB_can in h''. rewrite -Bl.GP.pow_bij in h''. trivial. trivial.
  move => h''. rewrite h''. simplify. apply (contraNneq false). move => h'''.
  apply h. smt(@Bl.GP.ZModE). trivial.
  (* starting casing 2, d correct *)
  case (result_R.`2 = aL); move => h.
  (* a = i *)
  rewrite h. rewrite (nth_mkseq). smt(Bl.t_valid). simplify. have : exp aL 1 = aL. smt(@Bl.GP.ZModE).
move => h'. rewrite h'. simplify.
  have : one / (aL + (one - aL)) = one.
  smt(@Bl.GP.ZModE). move => h''. rewrite h''.
  smt(@Bl.GP.ZModE @Bl.GB @Bl.GPB).
  (* a <> i *)
   rewrite (nth_mkseq). smt(Bl.t_valid). simplify.  have : exp aL 1 = aL. smt(@Bl.GP.ZModE).
  move => h'. rewrite h'. have : Bl.GB.g ^ asint result_R.`2 <>
  Bl.GB.g ^ asint aL. apply (contraNneq false). move => h''. apply h.
  rewrite Bl.exp_GB_can in h''. rewrite -Bl.GP.pow_bij in h''. trivial. trivial.
  move => h''. rewrite h''. simplify.
  rewrite H1 in H2. rewrite Bl.GT_shuffle2 in H2.
  rewrite mkKey_ga in H2. rewrite -Bl.GB.expB in H2. rewrite Bl.GP.log_bij in H2.
  rewrite !Bl.exp_gt_eq in H2. rewrite -Bl.GP.expB in H2. rewrite Bl.GP.loggK in H2.
   rewrite Bl.e_div1 in H2. rewrite Bl.log_e_gen in H2.  rewrite Bl.GB.logK in H2. rewrite -H2.
  rewrite -(Bl.GPB.expgK (Bl.GB.(/) result_R.`4 result_R.`6)).
  rewrite -Bl.exp_gb_eq. rewrite -Bl.GB.expM. apply Bl.exp_GB_can2.
  apply Bl.GP.pow_bij. rewrite Bl.exp_gb_eq. rewrite Bl.GPB.expgK.
  rewrite !Bl.GP.ZModE.asintK. move => @/Bl.GPB.loge.
  rewrite Bl.GPB.ZModE.inzmodK. rewrite Bl.order_eq.
  rewrite !Bl.GP.ZModE.inzmodM. rewrite -!Bl.GP.ZModE.inzmodK.
  rewrite !Bl.GP.ZModE.inzmodB. rewrite !Bl.GP.ZModE.asintK.
  pose x := Bl.GB.log (Bl.GB.(/) result_R.`4 result_R.`6).
  (* need to show x is non zero *)
  have : inzmod x <> zero. have : result_R.`4 <> result_R.`6. apply (contraNneq false).
  move => h'''. apply H0. have : (result_R.`5 - result_R.`3 = zero => result_R.`3 = result_R.`5).  smt(@Bl.GP.ZModE).
  move => g.  apply g.  rewrite -H2. rewrite h'''. smt(@Bl.GP.ZModE @Bl.GB). trivial.  move => h'''.
  move => @/x.  apply (contraNneq false). move => g. apply h'''. apply Bl.GB_zero. rewrite Bl.eq_inzmod in g.
  smt(@Bl.GB Bl.order_eq). smt(Bl.prime_q). smt(@Bl.GB). trivial. move => g.
  (* resuming *)
  rewrite !Bl.GP.ZModE.ZModpField.mul1r.
  rewrite Bl.GP.ZModE.ZModpField.invrM. trivial. smt(@Bl.GP.ZModE). 
  rewrite (Bl.GP.ZModE.ZModpField.mulrC _ (inv (inzmod x))).
  rewrite Bl.GP.ZModE.ZModpField.mulrA. rewrite Bl.GP.ZModE.ZModpField.divrr. trivial.
  smt(@Bl.GP.ZModE).
  (* misc *) 
  smt(). smt().
qed.

section Hiding.
(* The proof is reasonably complicated, we start by bounding the chance
  the advesary misbehaves or computes an evaluation point for the key *)

module HidingWithBad (A : AdvH) = {
   var bad : bool
  
  proc main() : bool = {
    var phi, a, key, c, d, js, phiis, j, i0, phi0, psi, w, temp1, temp2, ws, i, phii;
    phi <$ dpoly Bl.t coeff_sample;                        
    a <$ Bl.FD.dt;                                         
    key <- Bl.mkKey a;                                              
    (c, d) <- (prodEx key phi, tt);                            
    js <@ A.choose(key, c);
      if (a \in js) {
      bad <- true;
    } else {
      bad <- false;    
    }
    phiis <- map (fun (x1 : Bl.GP.exp) => peval phi x1) js;
    ws <- [];                                              
    j <- 0;                                                
    while (j < Bl.t - 1) {                                                 
      i0 <- nth zero js j;                                                                            
      phi0 <- peval phi i0;                                 
      psi <- (edivpoly phi (X - polyC i0)).`1;              
      w <- prodEx key psi;                                  
     (temp1, temp2) <- (phi0, w);                         
      ws <- temp2 :: ws;                                   
      j <- j + 1;                                          
    }                                                     
    (i, phii) <@ A.guess(phiis, ws);                       
    return  (phii = peval phi i /\
   ! (i \in js) /\ size js = Bl.t - 1 /\ uniq js);
  }
}.

(* EasyCrypt does not great support for sampling without replcament so we define the op axiomaticly *)
op js'_sample : exp -> exp list distr.
axiom js'_sample_ll a : is_lossless (js'_sample a).
axiom js'_sample_size a j : j \in js'_sample a=> size j = Bl.t -1.
axiom js'_uniq j a :j \in js'_sample a => uniq (a :: j).

(* We introduce a new game which is close the to DL reduction in the first half and the old game in the second half *)
module HidingWithBad2 (A : AdvH) = {
   var bad : bool
  
  proc main() : bool = {
    var phi, a,x, key, ga, js, js', phiis, phiis', j, i0, phi0, psi, w, temp1, temp2, ws, i, phii;
    a <$ Bl.FD.dt;                                         
    key <- Bl.mkKey a;                                              
    x <$ Bl.FD.dt;  
    ga <- Bl.GB.g ^ (asint x);  
    js <@ A.choose(key, ga);
    phiis' <$ dlist Bl.FD.dt (Bl.t-1);
      if (a \in js) {
      bad <- true;
    } else {
      bad <- false;    
    }
    js' <$ js'_sample a;
    phi <- interpolate (a::js')(x::phiis');
    phiis <- map (fun (x1 : Bl.GP.exp) => peval phi x1) js;
    ws <- [];                                              
    j <- 0;                                                
    while (j < Bl.t - 1) {                                                 
      i0 <- nth zero js j;                                                                            
      phi0 <- peval phi i0;                                 
      psi <- (edivpoly phi (X - polyC i0)).`1;              
      w <- prodEx key psi;                                  
     (temp1, temp2) <- (phi0, w);                         
      ws <- temp2 :: ws;                                   
      j <- j + 1;                                          
    }                                                     
    (i, phii) <@ A.guess(phiis, ws);                       
    return  (phii = peval phi i /\
   ! (i \in js) /\ size js = Bl.t - 1 /\ uniq js);
  }
}.

declare module A <: AdvH {-HidingWithBad.bad, -HidingWithBad2.bad}.

lemma Ad3_split &m :
    Pr[HidingWithBad(A).main() @ &m : res] 
      <= Pr[HidingWithBad(A).main() @ &m : res /\ !HidingWithBad.bad] + Pr[HidingWithBad(A).main() @ &m : HidingWithBad.bad].
proof.
  byequiv. proc. wp. call(_:true). while (={key,phi,j,ws,c,phiis,a,js}). auto.  progress. wp.
  call(_:true). auto. auto.
qed.

module Adv3 (Adv : AdvH) : Bl.TsdhAdv = {
  proc comp(ga: Bl.GB.group list) : exp * Bl.GB.group  = {
      var phi,  key, c, d, a, js, phiis, j, i0, phi0, psi, w, temp1, temp2, ws, i, phii;
      phi <$ dpoly Bl.t coeff_sample;                                                             
      key <- ga;                                         
      (c, d) <- (prodEx key phi, tt);                            
      js <@ A.choose(key, c);
        phiis <- map (fun (x1 : Bl.GP.exp) => peval phi x1) js;
        ws <- [];                                              
        j <- 0;                                                
        while (j < Bl.t - 1) {                                                 
        i0 <- nth zero js j;                                                                            
        phi0 <- peval phi i0;                                 
        psi <- (edivpoly phi (X - polyC i0)).`1;              
        w <- prodEx key psi;                                  
      (temp1, temp2) <- (phi0, w);                         
        ws <- temp2 :: ws;                                   
        j <- j + 1;                                          
    }                                                     
    (i, phii) <@ A.guess(phiis, ws);
     a <- nth zero js (find (fun x => Bl.GB.g ^ (asint x) = nth Bl.GB.g ga 1) js);
      return (one-a,Bl.GB.g);
    }
}. 


lemma Ad3_bad_prob &m :
  Pr[HidingWithBad(A).main() @ &m : HidingWithBad.bad] <= Pr[Bl.Tsdh(Adv3(A)).main() @ &m : res] .
proof.
  byequiv. proc. inline *. swap{1} 1 2. seq 4 6 : (={glob A, a,key,phi} /\ c{1} = c0{2} /\ d{1} = d0{2} /\ ga{2} = Bl.mkKey a{2}).
  auto. progress. wp. call(_:true).
while( ={a, key, phi, j,ws,phiis,js } /\ c{1} = c0{2} /\ d{1} = d0{2} /\ HidingWithBad.bad{1} = a{1} \in js{1}).
  auto. progress. auto. call(_:true). auto. progress. rewrite nth_mkseq. smt(Bl.t_valid). simplify.
  (* now to show equivlants of condiitions *)
  have : exp a{2} 1 = a{2}. smt(@Bl.GP.ZModE). move => g. rewrite g.
  pose x := nth zero result_R  (find (fun (x : Bl.GP.exp) => Bl.GB.g ^ asint x = Bl.GB.g ^ asint a{2}) result_R).
  have : x = a{2}. have : Bl.GB.g ^ asint x  = Bl.GB.g ^ asint a{2}. smt(@List). smt(@Bl).
  move => h''. rewrite h''. smt(@Bl.GP.ZModE.ZModpField). rewrite nth_mkseq. smt(Bl.t_valid).
  have : exp a{2} 1 = a{2}. smt(@Bl.GP.ZModE). move => g. simplify. rewrite g.
   pose x := nth zero result_R  (find (fun (x : Bl.GP.exp) => Bl.GB.g ^ asint x = Bl.GB.g ^ asint a{2}) result_R).
   have : x = a{2}. have : Bl.GB.g ^ asint x  = Bl.GB.g ^ asint a{2}. smt(@List). smt(@Bl).
   move => h''. rewrite h''. have : a{2} + (one - a{2}) = one. smt(@Bl.GP.ZModE.ZModpField). move => g'. rewrite g'.
      smt(@Bl.GB @Bl.GP.ZModE). smt().  smt().  
qed. 
  
(* we have now dealt with the case where the adverary learns an evaluation point from the key *)
lemma real_bad &m :
    Pr[Hiding(PolyComDLScheme, A).real() @ &m : res] = Pr[HidingWithBad(A).main() @ &m : res].
proof.
  byequiv. proc. call(_:true). while(={j,ws,key,phi,js}). inline *. auto. progress. auto. call(_:true). inline*. auto. progress.
  trivial. qed.

module AdvHtoDL : Bl.DLogAdv ={
  proc guess(ga : Bl.GB.group) = {
    var a, key; (* The secret and commitment scheme key *)
      var i, phii : exp; (* Adversary's response *)
      var js; (* opening to the commitment and list of point evaludated *)
      var phiis : exp list; (* eval at the points in js *)
      var ws : Bl.GB.group list; (* witness to evaluation *)
      var temp2;
      var j : int;

      a   <$ Bl.FD.dt;
      key <- Bl.mkKey a;
    
      (* construct evaluation points *)
      js <@ A.choose(key,ga);
      phiis <$ dlist Bl.FD.dt (Bl.t-1);
    
      ws <- [];
      j <- 0;
      while (j < Bl.t -1) {
        temp2 <- (Bl.GB.(/) ga (Bl.GB.g^ (asint (nth zero phiis j))))^(asint (one/(a-(nth zero js j))));
          ws <- temp2 :: ws;
        j <- j + 1;      
      }

      (* Need to construct a commitment (c, d) <- (prodEx key m, tt); *)

      (i, phii) <@ A.guess(phiis,ws);

      return  peval (interpolate (i :: js) (phii :: phiis)) a;
  }
}.

lemma HidingWithBadEquiv &m :
    Pr[HidingWithBad2(A).main() @ &m : res /\ !HidingWithBad2.bad] =
    Pr[HidingWithBad(A).main() @ &m : res /\ !HidingWithBad.bad].
proof. 
  byequiv. proc. inline *. swap{1} 8 -5. swap{2} [2..3] -1. seq 3 2 : (={glob A, a, key} /\ key{1} = Bl.mkKey a{1} /\
  size js'{1} = Bl.t-1 /\ uniq (a{1} :: js'{1})). rnd{1}. auto.
  progress. apply js'_sample_ll. apply (js'_sample_size aL); trivial. smt(js'_uniq @List). smt(js'_uniq @List).

  seq 7 5 : (={glob A,a,key, phiis,phi,js} /\ HidingWithBad2.bad{1} = HidingWithBad.bad{2} /\ key{1} = Bl.mkKey a{1} /\
  uniq (a{1} :: js'{1}) /\  size js'{1} = Bl.t-1).
  swap{1} 4 -2. wp. call(_:true). wp.

  rnd (fun (x : exp * exp list) => (interpolate (a{1}::js'{1})(x.`1::x.`2)))
  (fun x=> (peval x a{1}, map (peval x) js'{1})) : 0 0. auto. progress.
  (* poly to list to poly *) rewrite eq_sym. apply interpolate_corr. rewrite dmap_id in H2.
  rewrite supp_dpoly in H2. smt(Bl.t_valid). smt(@List). smt(@List). smt(@List). smt().
  (* poly to list poly prob *) rewrite dmap_id. apply interpolate_prob3. 
  (* poly to list poly prob *) rewrite dmap_id. apply interpolate_in_dpoly. smt(@List).
  have :  xphiis'L.`2 \in dlist Bl.FD.dt (Bl.t - 1). clear H2 H3. rewrite supp_dlet in H4. smt(@Distr).
  move => g. smt(@List @DList Bl.t_valid). 
  (* list to poly to list *) rewrite interpolate_corr2_head. smt(@List).
  have :  xphiis'L.`2 \in dlist Bl.FD.dt (Bl.t - 1). clear H2 H3. rewrite supp_dlet in H4. smt(@Distr).
  move => g. smt(@List @DList Bl.t_valid).  
  rewrite interpolate_corr2_tail. smt(@List).
  have :  xphiis'L.`2 \in dlist Bl.FD.dt (Bl.t - 1). clear H2 H3. rewrite supp_dlet in H4. smt(@Distr).
  move => g. smt(@List @DList Bl.t_valid). smt(). rewrite comPolEval. smt(interpolate_deg @List).
  rewrite interpolate_corr2_head. smt(@List). smt(@List). trivial.
  
  (* finishing up *)
  call(_:true). while (={glob A, a, key, phiis, phi, js,j,ws} /\
  HidingWithBad2.bad{1} = HidingWithBad.bad{2} /\
    key{1} = (Bl.mkKey a{1})%Bl /\ uniq (a{1} :: js'{1}) /\ size js'{1} = Bl.t - 1). auto. progress.
  auto. auto. auto.
qed.

lemma d_log &m :
 islossless A.guess =>  
 Pr[HidingWithBad2(A).main() @ &m : res /\ !HidingWithBad2.bad] <= Pr[Bl.DLogExp(AdvHtoDL).main() @ &m : res].
proof.
  move => h. byequiv. proc. inline *. swap{2} [1..2] 2.
  seq 2 2 : (={glob A, a,key} /\ key{1} = Bl.mkKey a{1}). auto.

  seq 3 3 : (={glob A, a,key,x,ga,js} /\ key{1} = Bl.mkKey a{1}  /\ ga{2} = Bl.GB.g ^ asint x{2}).
  auto. call (_:true). auto.

   (* stupid case 2 *)
  case (a{1} \in js{1}). wp. call{1} (_ : true ==> true). call{2} (_ : true ==> true).
  while (={j}). auto. wp. rnd{1}. auto. progress. apply js'_sample_ll. trivial. trivial.

  (* stupid case 1 *)
  case (size js{1} <> Bl.t-1). wp. call{1} (_ : true ==> true). call{2} (_ : true ==> true).
  while (={j}). auto. wp. rnd{1}. auto. progress. trivial. apply js'_sample_ll. trivial.

  (* stupid case 3*)
  case (! uniq js{1}). wp. call{1} (_ : true ==> true). call{2} (_ : true ==> true).
  while (={j}). auto.  wp. rnd{1}. auto. progress. trivial.  apply js'_sample_ll. trivial. 

  (* The first issue is to show the evaluation of the polynomials is equvilant *)
  seq 5 1 : (={glob A, a,key,x,ga,js,phiis} /\ key{1} = Bl.mkKey a{1}  /\ ga{2} = Bl.GB.g ^ asint x{2} /\
  ! (a{1} \in js{1}) /\ size js{1} = Bl.t - 1 /\ uniq (a{1} :: js'{1}) /\ size phiis{1} = Bl.t-1 /\
  phi{1} = interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1}) /\ size js'{1} = Bl.t-1 /\ size phiis'{1} = Bl.t - 1
  /\ uniq js{1} /\ phiis{2} = map (peval (interpolate (a{1} :: js'{1})(x{1} :: phiis'{1}))) js{1}). swap{1} 1 2.  wp.

  rnd (fun phiis=> map (peval (interpolate (a{1}::js'{1})(x{1}::phiis))) js{1})
  (fun phiis => map (peval (interpolate (a{1} :: js{1})(x{1} :: phiis))) js'{1}). auto. progress.

   apply js'_sample_ll.
  (* left right left *) rewrite inter_inter_tail. smt(@DList Bl.t_valid). smt(@DList Bl.t_valid js'_sample_size). 
    smt(js'_uniq). smt(@List). rewrite interpolate_corr2_tail. smt(@List). smt(@DList Bl.t_valid). trivial.
  (* right left right prob in *) rewrite !(AddDistr.dlist_mu1 _ _ Bl.GT.order). smt(@DList Bl.t_valid). smt(@Bl.FD).
    smt(@List js'_sample_size). smt(@Bl.FD). trivial. apply supp_dlist. smt(Bl.t_valid). split. smt(@List). apply allP. smt(@Bl.FD).
  (* right left right *) rewrite inter_inter_tail. smt(js'_sample_size @DList Bl.t_valid). smt(@DList Bl.t_valid). 
  smt(@List). smt(js'_uniq). rewrite interpolate_corr2_tail. smt(js'_uniq). smt(js'_sample_size @DList Bl.t_valid). trivial.
    smt(js'_uniq). smt(js'_uniq). smt(@List). smt(js'_sample_size). smt(@List js'_sample_size).

  (* witnesses *)
  wp. call(_:true). while (={glob A,  a, key, js, x, ga, phiis,j,ws} /\ key{1} = Bl.mkKey a{1} /\ ga{2} = Bl.GB.g ^ asint x{2} /\
  size js{1} = Bl.t -1 /\ 0 <= j{1} /\ ! (a{1} \in js{1}) /\ phi{1} = interpolate (a{1} :: js'{1}) (x{1} :: phiis'{1}) /\
    uniq js{1} /\ size phiis{1} = Bl.t -1 /\ size js'{1} = Bl.t-1 /\ size phiis'{1} = Bl.t-1 /\ uniq (a{1} :: js'{1}) /\
   phiis{2} = map (peval (interpolate (a{1} :: js'{1})(x{1} :: phiis'{1}))) js{1}).
    auto. progress. rewrite comPolEval. apply degDiv2. smt(interpolate_deg). 
  rewrite -Bl.GB.expB. rewrite -Bl.GB.expM. apply Bl.exp_GB_can2. apply Bl.GP.pow_bij. rewrite Bl.GP.ZModE.asintK.
  rewrite Bl.GP.ZModE.inzmodM. rewrite Bl.GP.ZModE.inzmodB. rewrite !Bl.GP.ZModE.asintK. pose i := nth zero js{2} j{2}.
  have : a{2} <> i. smt(@List). move => g. rewrite prt_eval. smt(@Bl.GP.ZModE). congr. rewrite interpolate_corr2_head.
  smt(@List). smt(@List). smt(@List). smt(@Bl.GP.ZModE). smt().

  auto. progress. rewrite H18. have : (peval (interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1})) result_R.`1 :: 
    map (peval (interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1}))) js{2}) =
    map (peval (interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1}))) (result_R.`1::js{2}). smt(@List). move => g. rewrite g.
    rewrite inter_inter. smt(). smt(). smt(). apply interpolate_corr2_head. smt(). smt(). trivial. trivial.
qed.

lemma PolyComDLScheme_Hiding  &m :
 islossless A.guess =>   
 Pr[Hiding(PolyComDLScheme, A).real() @ &m : res] <=
 Pr[Bl.DLogExp(AdvHtoDL).main() @ &m : res] + Pr[Bl.Tsdh(Adv3(A)).main() @ &m : res].
 proof.
 move => h. rewrite real_bad. have : forall (b a c : real), a <= b => b <= c => a <= c. smt(). move=> h'.
   apply (h' (Pr[HidingWithBad(A).main() @ &m : res /\ !HidingWithBad.bad] + Pr[HidingWithBad(A).main() @ &m : HidingWithBad.bad])).
   apply Ad3_split. have : forall (a a' b b':real), a <= a' => b <= b' => a + b <= a' + b'. smt().
   move => g. apply g. rewrite -HidingWithBadEquiv.  apply d_log; trivial. apply Ad3_bad_prob.
 qed.


end section Hiding.


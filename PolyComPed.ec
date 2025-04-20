(* Constant-Size Commitments to Polynomials and Their Applications - PolyComPed *)
require Poly Bigop.
require import AllCore PolyCom Bilinear List IntDiv Ring Bigalg AddList AddPoly DBool Real DList Distr Dexcepted AddDistr.

clone Bilinear.Bl as Bl.

clone AddPoly as PolyHelp.

import PolyHelp.
import BasePoly.
 
clone export PolynomialCommitment as PolyComPed with
  type ck <- (Bl.GB.group) list * (Bl.GB.group) list,
  type witness <- (Bl.GP.exp * Bl.GB.group),
  type commitment <- Bl.GB.group, 
  type openingkey <- poly,
  type coeff <- Bl.GP.exp,
  op t <- Bl.t,
  axiom t_valid <- Bl.t_valid,
  theory IDCoeff <- R,
  theory BasePoly <- BasePoly,
  op coeff_sample <= Bl.FD.dt.
  
    
    import PolyHelp.

  import Bl.GP.ZModE.


  abbrev ( ^ ) = Bl.GB.( ^ ).

    (* Define the key algortihms and related lemmas *)
 (*  let h : Bl.GB.g. *)
  op mkKey(g : Bl.GB.group)(a : exp) =
    mkseq (fun (i:int) =>
    (g^(asint (exp a i))))
  (Bl.t + 1).
  
  op prodEx (g : Bl.GB.group)(x : Bl.GB.group list)(m : poly) =
    List.foldr Bl.GB.( * ) Bl.GB.e (* Prod *)
      (mkseq (fun (i : int) => Bl.GB.( ^ )(nth g x i)
          (asint m.[i])) (size x + 1)).


        (* We first want to prove we can rephrase the combination of mkKey and prodEx in
            a way more favorable to induction *)
  lemma mkKey_ga g a : nth Bl.GB.g (mkKey g a) 1 = g ^ (asint a).
     rewrite nth_mkseq. smt(Bl.t_valid). simplify. smt(@Bl.GP.ZModE).
  qed.
      
  lemma prodExSimp g a m : size m <= Bl.t => prodEx g (mkKey g a) (polyL m) =
    List.foldr Bl.GB.( * ) Bl.GB.e (mkseq (fun (i : int) =>
      Bl.GB.( ^ )(nth g (mkseq (fun (i:int) =>  g^(asint
                  (exp a i))) (Bl.t+1)) i)
          (asint (polyL m).[i])) (size m + 1)).
  proof.
    move => h @/prodEx @/mkKey. apply foldr_eq_partR. smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB).
    rewrite !size_mkseq. smt().
    (* Equal *) rewrite !size_mkseq. rewrite take_mkseq. smt().
    have : (max 0 (size m + 1)) = size m + 1. smt(@List). move => h'. rewrite h'. apply eq_mkseq.
    move => x. simplify. trivial.
    (* Null *) rewrite !size_mkseq. rewrite (all_nth _ Bl.GB.g). move => i h'.
    simplify. rewrite nth_drop. smt(@List). smt(@List). rewrite nth_mkseq. split. smt(@List). move => h''. rewrite size_drop in h'. smt(@List).
    rewrite size_mkseq in h'. smt().
    simplify. have : (polyL m).[max 0 (size m + 1) + i] = Bl.GP.ZModE.zero. have : deg (polyL m) <= size m. apply degL_le.
    move => g'. apply gedeg_coeff. smt(@BasePoly). move => h''. rewrite h''. rewrite Bl.exp0_cus. trivial.
  qed.

  lemma prodEx_polyC g x c : prodEx g x (polyC c) =
      Bl.GB.( ^ ) (head g x) (asint c).
  proof.
    move => @/prodEx.  rewrite mkseqSr. smt(@List). simplify.
    rewrite foldr_id. smt(@Bl.GB). apply (all_nth _ Bl.GB.e).
    move => i ip. rewrite size_mkseq  in ip. simplify.
    rewrite nth_mkseq. have : max 0 (size x) = size x. smt(@List).
    move => h. smt(). move => @/(\o). simplify.
    have : 1 + i <> 0. smt(). move => h. 
    rewrite polyCE. rewrite h. simplify.
    have : asint zero = 0. smt(@Bl.GP). smt(@Bl.GB).
    rewrite polyCE. simplify. smt(@List @Bl.GB).
  qed.
  
   lemma comPolEvalSub g (a : exp) m : 
    foldr Bl.GB.( * ) Bl.GB.e (mkseq (fun (i : int) =>
        g ^ (asint (exp a i)) ^
        (asint (polyL m).[i]))
     (size m + 1)) =
     g ^ (asint (peval (polyL m) a)).
  proof.
    rewrite PolyHelp.peval_simp. rewrite -(Bl.prod_sum_eq _ Bl.GP.ZModE.zero _). rewrite size_mkseq.
    apply foldr_eq_partR. smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). rewrite !size_mkseq. smt(degL_le).
    (* Show the first bit is equal *)
    rewrite size_mkseq. apply (eq_from_nth Bl.GB.g). rewrite !size_mkseq. rewrite size_take.
    smt(@BasePoly). rewrite size_mkseq. smt(degL_le). move => i h. rewrite nth_mkseq. rewrite size_mkseq in h. split. smt(). move => g'.
    smt(@BasePoly).
    rewrite nth_take. smt(@BasePoly @List). smt(@BasePoly @List). rewrite nth_mkseq. rewrite size_mkseq in h. split. smt(). move => g'.
    have : deg (polyL m) <= size m. apply degL_le. move => h'.
    smt(). simplify. rewrite nth_mkseq. rewrite size_mkseq in h.
    smt(). simplify.
    rewrite -Bl.GB.expM. apply eq_sym. rewrite mulrC. apply Bl.exp_GB_asint_mul. 
    (* Show the trail is nothing *)
    rewrite size_mkseq. rewrite (all_nth _ Bl.GB.e). move => i h. simplify. rewrite nth_drop.
    smt(). smt(). rewrite nth_mkseq. rewrite size_drop in h. smt(@List).    rewrite size_mkseq in h. smt(@BasePoly). simplify.
    have : forall a b, b = 0 => a^b = Bl.GB.e. smt(@Bl.GB). move => h''.  apply h''.
    rewrite -Bl.GP.ZModE.zeroE. apply Bl.GP.ZModE.asint_eq. apply gedeg_coeff. smt(degL_le).
  qed. 
        
  lemma comPolEval g a m : deg m <= Bl.t =>
      prodEx g (mkKey g a) m = g ^ (asint (peval m a)).
  proof.
    move => h. case : (surj_polyL m Bl.t h). move => s h'. elim h'; move => h' h''.
    rewrite h''. rewrite (prodExSimp g). smt(). rewrite (mkseq_nth_mkseq g g). smt(@List).
    smt(@List). simplify.  apply comPolEvalSub.
  qed.
  
  lemma head_mkKey g a : head Bl.GB.g (mkKey g a) = g.
  proof.
    move => @/mkKey. rewrite mkseqSr. trivial. simplify.
    have : exp a 0 = one. move => @/exp. simplify. smt(iterop0). move => h'. smt(Bl.t_valid). smt(@Bl).
  qed.
   
 (* Now we are ready to define the main commitment scheme *)

  (* PK = g, g^a, . . ., g^a^t, h, h^a, . . ., h^a^t *)
      module PolyCommitPed : PC_Scheme =
      {

        var bad : bool (* a bookkeeping variable for a fail mode in privacy *)
        
        proc setup() : (Bl.GB.group list) * (Bl.GB.group list) =
        {
          var a, b : Bl.GP.exp;
          var pk1, pk2 : Bl.GB.group list;

          a <$ Bl.FD.dt;
          pk1 <- mkKey Bl.GB.g a;
          b <$ (Bl.FD.dt);

         if (b = zero) {
              bad <- true;
         } else {
              bad <- false;    
         }
          
          pk2 <- mkKey (Bl.GB.( ^ ) Bl.GB.g (asint b)) a;

          return (pk1, pk2);
        }
        
(* C =( Prod_(j=0)^t (g^a_j)^(phi_j) ) ( * ) ( Prod_(j=0)^t (h^a_j)^(phi1_j) )
*)
     proc commit(x : (Bl.GB.group list) * (Bl.GB.group list), m : poly) :
            Bl.GB.group * poly =
        {
          var m1;
          m1 <$ dpoly (size x.`1 -1) Bl.FD.dt;
          return (Bl.GB.( * ) (prodEx (head Bl.GB.g x.`1) x.`1 m)
                              (prodEx (head Bl.GB.g x.`2) x.`2 m1), m1);
        }

 (* Outputs the committed polynomials *)
    proc open(x : (Bl.GB.group list) * (Bl.GB.group list), c : Bl.GB.group, m : poly, d : poly) : poly =
        {
          var c', c'';
          c' <- prodEx (head Bl.GB.g x.`1) x.`1 m;
          c'' <- prodEx (head Bl.GB.g x.`2) x.`2 d;

          return (if(c = Bl.GB.( * ) c' c'') then (m) else poly0);
        }

  (* Checks polynomial matches commit *)
            proc verifypoly(x : (Bl.GB.group list) * (Bl.GB.group list), c : Bl.GB.group, m : poly, d : poly) : bool =
        {
          var c', c'';
          c' <- prodEx (head Bl.GB.g x.`1) x.`1 m;
          c'' <- prodEx (head Bl.GB.g x.`2) x.`2 d;

          return (deg m <= Bl.t /\ deg d <= Bl.t /\ c = Bl.GB.( * ) c' c'');
        }

 (* Sample the polynomial at the point and create the witness *)
            proc createwitness(x : (Bl.GB.group list) * (Bl.GB.group list), m : poly, i : Bl.GP.exp, d : poly) : Bl.GP.exp * (Bl.GP.exp * Bl.GB.group) =
        {
          var w;
          var phi : Bl.GP.exp;
          var phi1 : Bl.GP.exp;
          var psi;
          var psi1;
          
          phi <- peval m i;
          phi1 <- peval d i;

          psi <- (edivpoly m (X-polyC i)).`1;
          psi1 <-(edivpoly d (X-polyC i)).`1; 

          w <- Bl.GB.( * ) (prodEx (head Bl.GB.g x.`1) x.`1 psi)
          (prodEx (head Bl.GB.g x.`2) x.`2 psi1);

          return (phi, (phi1, w));
        }

  (* e(C,g) ?= e(w_i , g_a/g^i)e(g^phi(i) * h^phi1(i) , g) *)
            proc verifyeval(x : (Bl.GB.group list) * (Bl.GB.group list), c : Bl.GB.group, i : Bl.GP.exp, phi : Bl.GP.exp, w : Bl.GP.exp*Bl.GB.group) : bool =
        {
          var r , r';
          
          r <- Bl.e w.`2 (Bl.GB.( / ) (nth Bl.GB.g x.`1 1) (Bl.GB.g^(Bl.GP.ZModE.asint i)));
          r' <- Bl.e (Bl.GB.( * ) (Bl.GB.( ^ )Bl.GB.g (asint phi))
          (Bl.GB.( ^ ) (head Bl.GB.g x.`2) (asint w.`1))) Bl.GB.g;

          return Bl.e c Bl.GB.g = Bl.GT.( * ) r r';
        }
    }.

  lemma PolyComDL2_Corr :
  hoare[Correctness(PolyCommitPed).main : true ==> res].
  proof.
     proc. inline*. auto. progress. case (Bl.t{hr} < deg p{hr}). smt(). move => h'.
    simplify. 
    (* Lift everything to exp *)
    rewrite size_mkseq in H1.
    (* deg lemma *)
    have : deg m10 <= Bl.t{hr}. have : deg m10 <= max 0 (Bl.t{hr} + 1) - 1.
    have : 0 <= Bl.t{hr}. smt(Bl.t_valid). move => h''.
    smt(supp_dpoly). move => h''. smt(Bl.t_valid). move => h''.
    split. smt(@Bl).
    (* resum main 0 suing comPolEval *)
    rewrite !head_mkKey. 
    rewrite comPolEval. smt(). rewrite comPolEval. trivial.
    rewrite comPolEval. apply (lez_trans (deg p{hr})). apply degDiv.  smt().
    (* preparing to use the map *)
    rewrite -Bl.GB.expM.  rewrite -Bl.GB.expD.  rewrite Bl.e_pow1. rewrite Bl.e_g_g.
    rewrite -Bl.GB.expM. rewrite -Bl.GB.expD. rewrite Bl.e_pow1. rewrite Bl.e_g_g.
     rewrite mkKey_ga. rewrite comPolEval.  apply (lez_trans (deg m10)). apply degDiv.  smt().
    rewrite - Bl.GB.expM. rewrite -Bl.GB.expD.
    rewrite -Bl.GB.expB. rewrite Bl.e_pow. rewrite Bl.e_g_g.
    (* We have g ^ a = g ^ b, we want to use the bijection but we
    can't until asint is removed *)
    rewrite !Bl.exp_GT_asint_add_l. rewrite !inzmodM !asintK. rewrite Bl.GT.expM.
    rewrite !Bl.exp_GT_asint_add_l. rewrite !inzmodM !asintK. rewrite -Bl.GP.expM.
    rewrite -Bl.GP.expD. apply Bl.GP.pow_bij.
    (* Reasoning of polynomial *)
    have : forall (a b c d e : exp),
  (a + b) * c + (d + e) = (a * c + d) + (b * c + e).
  move => ? ? ? ? ?. rewrite ZModpField.mulrDl. smt(@ZModpField).
  move => h'''. rewrite h'''.
    rewrite (polyRemThem_corr p{hr} (X- polyC i{hr})). apply Xi_neq_0. rewrite -peval_add.
    rewrite -(polyRemThem_corr p{hr}(X- polyC i{hr})). apply Xi_neq_0.
    rewrite (polyRemThem_corr m10 (X- polyC i{hr})). apply Xi_neq_0. rewrite -peval_add.
    rewrite -(polyRemThem_corr m10 (X- polyC i{hr})). apply Xi_neq_0.
    have : forall (a b c d :exp), a = b => c = d => a + c = b + d.
    smt(). move => g. apply g.
    (* prove for p *)
    rewrite -polyRemThem_r. rewrite peval_polyC. rewrite -peval_over_Xi.
    rewrite -peval_add. rewrite peval_X. rewrite -peval_neg.
    rewrite peval_polyC. trivial.
    (* prove for m10 *)
    rewrite -polyRemThem_r. rewrite peval_polyC. rewrite -peval_over_Xi.
    rewrite -peval_add. rewrite peval_X. rewrite -peval_neg.
    rewrite peval_polyC. trivial.
    have : forall (a b c : exp), a * (b + c) = (a * b) + (a * c).
  move => ? ? ?. rewrite ZModpField.mulrC. rewrite ZModpField.mulrDl.
  smt(@ZModpField). move => g'. rewrite g'.
    smt(@Bl.GP).
qed.

axiom expg_modz_gen (b : Bl.GB.group) k : b ^ (k %% Bl.GB.order) = b ^ k.

axiom expe (b :  Bl.GB.group) : Bl.GPB.loge b <> Bl.GPB.ZModE.zero <=> b <> Bl.GB.e.

op isValid (k : (Bl.GB.group * Bl.GB.group) list)  =
  all (fun (y : Bl.GB.group) => y <> Bl.GB.e) (unzip2 k).


  op factorFind : poly -> Bl.GB.group list -> exp.
  axiom factorFindCorr p p' a : p <> p' =>
  peval p a = peval p' a =>
    factorFind (p - p')
  (map (fun (i : int) => Bl.GB.g ^ asint (exp a i))
     (range 0 (Bl.t + 1))) = a.

   lemma not_inv (x : exp) : one - x <> - x.
       have : forall (a b c : exp), a <> c + b => a - b <> c.
       smt(@Bl.GP.ZModE). move => h. apply h. smt(@Bl.GP.ZModE).
     qed.

  section Security.

  declare module A_PB <: AdvPB {-PolyCommitPed.bad}.
    
  module Adv  : Bl.TsdhAdv2 = {
    proc comp(h : (Bl.GB.group * Bl.GB.group) list) : (exp -> exp) * (exp -> Bl.GB.group) = {
      var c, phi, phi', d, d';
      (c, phi, phi', d, d') <@ A_PB.forge(unzip1 h, unzip2 h);
      return (if (prodEx Bl.GB.g (unzip1 h) phi = prodEx Bl.GB.g (unzip1 h) phi') then
        ((fun e => one - factorFind (phi - phi') (unzip1 h)), (fun e=>Bl.GB.g))
      else
       ((fun (e : exp)  => (peval phi' e - peval phi e) / (peval d e - peval d' e)), (fun e => Bl.GB.g)));
    }
  }.
  
  lemma PolyComDLScheme_PolynomialBinding &m  :
        Pr[PolynomialBinding(PolyCommitPed, A_PB).main() @ &m : res]  <=
        Pr[Bl.Tsdh2(Adv).main() @ &m :res].
  proof. 
    byequiv. proc. inline *. auto. call (_ : true). auto. progress.
    (* key valid *)
    rewrite unzip1_zip. smt(@List). trivial. rewrite unzip2_zip. smt(@List). trivial.
    (* starting by cleaning validity h*)
    rewrite H6 in H9. rewrite head_mkKey in H9.
    rewrite comPolEval in H9; trivial. rewrite head_mkKey in H9.  rewrite comPolEval in H9; trivial.
    rewrite comPolEval in H9; trivial. rewrite comPolEval in H9; trivial.
    (* First case *)
    case ( peval result_R.`2 aL = peval result_R.`3 aL); move => h. right. rewrite unzip1_zip. smt(@List).
    rewrite !comPolEval; trivial. rewrite h. simplify.  rewrite factorFindCorr. trivial. trivial. split. apply not_inv.
    have : aL + (one - aL) = one. smt(@Bl.GP.ZModE.ZModpField). move => g. rewrite g. smt(@Bl.GB @Bl.GP.ZModE).
    (* Second case *)
    left. rewrite unzip1_zip. smt(@List). rewrite !comPolEval; trivial. have :  Bl.GB.g ^ asint (peval result_R.`2 aL) <>
    Bl.GB.g ^ asint (peval result_R.`3 aL). apply (contraNneq false). move => h'. apply h. rewrite Bl.exp_GB_can in h'.
    rewrite -Bl.GP.pow_bij in h'. trivial. trivial. move => h'. rewrite h'. simplify.
    rewrite -!Bl.GB.expM in H9. rewrite -!Bl.GB.expD in H9. rewrite Bl.exp_GB_can2 in H9. rewrite -Bl.GP.pow_bij in H9.
    rewrite !Bl.GP.ZModE.inzmodD in H9. rewrite !Bl.GP.ZModE.inzmodM in H9. rewrite !Bl.GP.ZModE.asintK in H9.
    have : (peval result_R.`4 aL - peval result_R.`5 aL) <> zero. apply (contraNneq false). move => h''. apply h.
    smt(@Bl.GP.ZModE). trivial. move => h'''. have : forall (a a' b c c' : exp), a + b * c = a' + b * c' => a'-a = b * (c-c').

    smt(@Bl.GP.ZModE). move => h''''. apply h'''' in H9. smt(@Bl.GP.ZModE).
    (* Misc *)
    smt(). smt(). 
  qed.

  declare module A_EB <: AdvEB {-PolyCommitPed.bad}.
  
  module Adv2 : Bl.TsdhAdv2 = {
    proc comp(h : (Bl.GB.group * Bl.GB.group) list) : (exp ->  exp) * (exp -> Bl.GB.group)  = {
      var c, i, phi, phi', d, d';
      (c, i, phi, d, phi', d') <@ A_EB.forge(unzip1 h, unzip2 h);
      return (if (d.`2 <> d'.`2) then
        if (Bl.GB.g^(asint i) = nth Bl.GB.g (unzip1 h) 1) then
        ((fun e => one - i), (fun e => Bl.GB.g)) else 
        ((fun e => -i), (fun e => (Bl.GB.( / ) d.`2 d'.`2)^(asint (one/(phi' + e*d'.`1-(phi+e*d.`1))))))
      else
       ((fun e => (phi' - phi) / (d.`1 - d'.`1)),(fun e=> Bl.GB.g)));
    }
  }.

  
  lemma PolyDL2_eval_sound &m :
      Pr[EvaluationBinding(PolyCommitPed, A_EB).main() @ &m :res] <=
      Pr[Bl.Tsdh2(Adv2).main() @ &m : res].
   proof.   
     byequiv. proc. inline*. auto. call(:true). auto. progress.
     (* key valid *)
    rewrite unzip1_zip. smt(@List). trivial. rewrite unzip2_zip. smt(@List). trivial.
     (* clean up hyp *)
     rewrite !head_mkKey in H4. rewrite !mkKey_ga in H4. rewrite -Bl.GB.expB in H4.
     rewrite !head_mkKey in H5. rewrite !mkKey_ga in H5. rewrite -Bl.GB.expB in H5.
     (* Our assumpation H3 and H4 now look the same as on page 21 of the paper *)
   
     (* case 1 - the witness group elements are diffirent  *)
     case (result_R.`4.`2 <> result_R.`6.`2); simplify => h. right. rewrite H4 in H5. clear H4.
     (* case 1 contains two subcases, only one is covered by the cases *)
     case (result_R.`2 = aL); move => h'. rewrite h'. rewrite unzip1_zip. smt(@List Bl.t_valid). rewrite (nth_map 0).
     smt(@List Bl.t_valid). simplify. rewrite nth_range. smt(Bl.t_valid). simplify. have : exp aL 1 = aL. smt(@Bl.GP.ZModE).
     move => h''. rewrite h''. simplify.
     have : one / (aL + (one - aL)) = one.
     smt(@Bl.GP.ZModE). move => h'''. rewrite h'''.
     smt(@Bl.GP.ZModE @Bl.GB @Bl.GPB).

     (* case 1 - subcase 2 *)
     rewrite unzip1_zip. smt(@List Bl.t_valid). rewrite (nth_map 0). smt(@List Bl.t_valid). rewrite (nth_range).
     smt(@List Bl.t_valid). simplify. have : exp aL 1 = aL. smt(@Bl.GP.ZModE).
     move => h''. rewrite h''. have : Bl.GB.g ^ asint result_R.`2 <>
    Bl.GB.g ^ asint aL. apply (contraNneq false). move => h'''. apply h.
     rewrite Bl.exp_GB_can in h'''. rewrite -Bl.GP.pow_bij in h'''. trivial. trivial. move => h'''. rewrite h'''. simplify.
     rewrite -!Bl.GB.expM in H5. rewrite -!Bl.GB.expD in H5. apply Bl.e_mul_gen in H5.
     rewrite inzmodB in H5. rewrite !inzmodD in H5. rewrite !inzmodM in H5. rewrite !asintK in H5.
     apply (Bl.exp_ab_c _ _ _ _ _ _) in H5.  apply (contraNneq false). move => h''''. apply h. 
     have : inzmod ((Bl.GB.log result_R.`4.`2)) = inzmod ((Bl.GB.log result_R.`6.`2)). rewrite Bl.exp_add_right in H5.
     rewrite Bl.exp_mul_left in H5. smt(@Bl.GP.ZModE). smt(@Bl.GP.ZModE).
   move => g. rewrite -Bl.GB.expgK. rewrite eq_sym. rewrite -Bl.GB.expgK. rewrite -eq_inzmod in g.
     smt(Bl.order_eq @Bl.GB). trivial. trivial. split. smt(@Bl.GP.ZModE). rewrite -H5. rewrite eq_sym.
     rewrite Bl.GP.ZModE.mulE. rewrite -Bl.order_eq. rewrite Bl.GB.expg_modz. rewrite Bl.GB.expM.
     rewrite Bl.GP.ZModE.addE. rewrite Bl.GP.ZModE.oppE. rewrite !Bl.GP.ZModE.inzmodK. rewrite -!Bl.order_eq.
     rewrite Bl.GB.expg_modz. rewrite Bl.GB.expD. rewrite !Bl.GB.expg_modz. rewrite Bl.GB.expN. rewrite !Bl.GB.expg_modz.
     rewrite !Bl.GB.expgK. have : forall a, 1 %% Bl.GB.order * a = a. smt(Bl.order_eq @IntDiv Bl.prime_q @Bl.GP.ZModE.ZModpField).
   move => g. rewrite g. apply Bl.exp_GB_can2_gen. apply (contraNneq false). move => h''''. apply h. smt(@Bl.GPB). 
     trivial. rewrite Bl.order_eq. rewrite -Bl.GP.ZModE.inzmod_mod. trivial.

     (* case 2 *)
     left.
     have : (Bl.e (Bl.GB.( * ) (Bl.GB.g ^ (Bl.GP.ZModE.asint result_R.`5)) (Bl.GB.g ^ asint b0L ^ asint result_R.`6.`1)) Bl.GB.g) =
     (Bl.e (Bl.GB.( * ) (Bl.GB.g ^ asint result_R.`3) (Bl.GB.g ^ asint b0L ^ asint result_R.`4.`1))%Bl.GB Bl.GB.g).
       rewrite H4 in H5. clear H4. rewrite Bl.GT_shuffle2 in H5. apply Bl.GT_zero. rewrite -H5. smt(@Bl.GP). move => h'.
       rewrite Bl.GP.log_bij in h'.
     rewrite !Bl.log_e_gen in h'. rewrite -!Bl.GB.expM in h'. rewrite -!Bl.GB.expD in h'. rewrite !Bl.GB.logK in h'.
     rewrite Bl.GB_one in h'. rewrite !inzmodM in h'. rewrite Bl.order_eq in h'. rewrite -!inzmod_mod in h'.
     rewrite !inzmodD in h'. rewrite !inzmodM in h'.  rewrite !asintK in h'. rewrite !Bl.GP.ZModE.ZModpField.mulr1 in h'.
     apply Bl.exp_a_bc. smt(@ZModpField). trivial.
    (* nonsense *)
    smt(). smt().
   qed.

 module HidingSimp (A : AdvH) = {

  var bad : bool

  (* first we move to this game *)
   proc comm_sim() : bool = {
     var key; (* The polynomial and commitment scheme key *)
      var c : Bl.GB.group; (* Commitment to the polynoimal *)
      var i, phii : exp; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis;
      var ws : (exp * Bl.GB.group) list; (* witness to evaluation *)
      var  phi;
      var j : int;
      var a, b, pk1, pk2, m1, phi0, phi1, psi, psi1, w, temp1, temp2;                
     a <$ Bl.FD.dt;                                                 
     pk1 <- mkKey Bl.GB.g a;                                               
     b <$ Bl.FD.dt;                                       
     if (b = zero) {                                       
        HidingSimp.bad <- true;                                                        
     } else {                                                                       
        HidingSimp.bad <- false;                                              
     }                                                                              
     pk2 <- mkKey (Bl.GB.g ^ asint b) a;                             
     key <- (pk1, pk2);                                                                
      m1 <$ dpoly Bl.t Bl.FD.dt;                
     c <- prodEx (head Bl.GB.g pk1) pk1 m1;                                                                               
     js <@ A.choose(key, c);
         phi <$ dpoly Bl.t Bl.FD.dt;
     d <- ((inv b) ** (m1  - phi));
     phiis <- map  (fun (x1 : Bl.GP.exp) => peval phi x1) js;
       ws <- [];                                                      
       j <- 0;                                             
       while (j < Bl.t - 1) {                                                                 
       i <- nth zero js j;                                                                 
       phi0 <- peval phi i;                                                                
       phi1 <- peval d i;                                                           
       psi <- (edivpoly phi (X - polyC i)).`1;                                        
       psi1 <- (edivpoly d (X - polyC i)).`1;                                              
       w <- Bl.GB.( * )                                                                                 
       (prodEx (head Bl.GB.g key.`1) key.`1                                               
         psi)                                                                         
        ( prodEx (head Bl.GB.g key.`2) key.`2                                               
         psi1);                                                                    
       (temp1, temp2) <- (phi0, (phi1, w));                                            
         ws <- temp2 :: ws;                                                             
         j <- j + 1;                                                                         
     }                                                                                    
     (i, phii) <@ A.guess(phiis, ws);
     return phii = peval phi i /\ size js = Bl.t - 1 /\  !(i \in js)  /\ size js = Bl.t-1 /\ uniq js;
    }
   
    (* then this game *)
    proc real() : bool = {
      var key; (* The polynomial and commitment scheme key *)
      var c : Bl.GB.group; (* Commitment to the polynoimal *)
      var i, phii : exp; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis : (exp * exp list); (* eval at the points in js *)
      var ws : (exp * Bl.GB.group) list; (* witness to evaluation *)
      var temp2, js_1;
      var j : int;
      var a, b, pk1, pk2, m1;

      a <$ Bl.FD.dt;               
      pk1 <-  mkKey Bl.GB.g a;           
      b <$ Bl.FD.dt;

       if (b = zero) {
              bad <- true;
         } else {
              bad <- false;    
         }
     
      pk2 <- mkKey (Bl.GB.g ^  asint b) a;             
      key <- (pk1, pk2);           
      m1 <$ dpoly (size pk1 - 1)  Bl.FD.dt;                
      (c, d) <- ((prodEx (head Bl.GB.g pk1) pk1 m1)%Bl.GB, m1);

      (* construct evaluation points *)
      js <@ A.choose(key, c);
      if (size js = Bl.t -1) {
      js_1 <$ dcond Bl.FD.dt (fun x => ! x \in js);
      phiis <$ Bl.FD.dt `*` dlist Bl.FD.dt (Bl.t-1);
      
      ws <- [];
      j <- 0;
      while (j < Bl.t -1) {
        temp2 <- ((peval d (nth zero js j)  - (nth zero phiis.`2 j)) / b,
          prodEx (head Bl.GB.g pk1) pk1 (edivpoly d (X - polyC (nth zero js j))).`1);
        ws <- temp2 :: ws;
        j <- j +1;
      }  
      
      (i, phii) <@ A.guess(phiis.`2,ws);
      } else {
          i <- zero;
          js_1 <- zero;
          phii <- zero;
          phiis <- (zero, []);
      }

      return (phii = peval (interpolate (js_1 :: js) (phiis.`1 :: phiis.`2))  i /\  !(i \in js)  /\ size js = Bl.t-1) /\ uniq js;
    }

    (* and finally this game *)
    proc rand() : bool = {
      var key; (* The polynomial and commitment scheme key *)
      var c : Bl.GB.group; (* Commitment to the polynoimal *)
      var i, phii : exp; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis : exp list; (* eval at the points in js *)
      var ws : (exp * Bl.GB.group) list; (* witness to evaluation *)
      var temp2,  js_1, phiis_1;
      var j : int;
      var a, b, pk1, pk2, m1;

      a <$ Bl.FD.dt;               
      pk1 <-  mkKey Bl.GB.g a;           
      b <$ Bl.FD.dt;               
      pk2 <- mkKey (Bl.GB.g ^  asint b) a;             
      key <- (pk1, pk2);           
      m1 <$ dpoly (size pk1 - 1)  Bl.FD.dt;                
      (c, d) <- ((prodEx (head Bl.GB.g pk1) pk1 m1)%Bl.GB, m1);

      (* construct evaluation points *)
      js <@    A.choose(key,c);
      if (size js = Bl.t -1) {
      js_1 <$  dcond  Bl.FD.dt (fun x => ! x \in js);
      phiis_1 <$ Bl.FD.dt;
      phiis   <$  dlist Bl.FD.dt (Bl.t-1);
      
      ws <- [];
      j <- 0;
      while (j < Bl.t -1) {
        temp2 <- ((peval d (nth zero js j)  - (nth zero phiis j)) / b,
          prodEx (head Bl.GB.g pk1) pk1 (edivpoly d (X - polyC (nth zero js j))).`1);
        ws <- temp2 :: ws;
        j <- j +1;
      }  
      
      (i, phii) <@ A.guess(phiis,ws);
       } else {
          i <- zero;
          js_1 <- zero;
           phii <- zero;
           phiis_1 <- zero;
          phiis <- [];
      }

      return (phii = peval (interpolate (js_1 :: js) (phiis_1 :: phiis))  i /\ !(i \in js)  /\ size js = Bl.t-1);
    }
  }.

     declare module A_H <: AdvH {-PolyCommitPed.bad, -HidingSimp.bad}.

  lemma count_not_x x : count (fun (x0 : Bl.GP.exp) => x0 <> x) (map inzmod (range 0 Bl.GT.order)) = Bl.GT.order -1.
  proof.
    have : uniq (map inzmod (range 0 Bl.GT.order)). smt(@List @Bl.GP.ZModE). move => h.
    have : Bl.GT.order = size  (map inzmod (range 0 Bl.GT.order)). smt(@List). move => h'. rewrite h'.
    rewrite countC. rewrite !size_map. rewrite !size_range. rewrite count_uniq_mem. smt(@Bl.GT).
    smt(@Bl.GP.ZModE).
  qed.

  lemma mu_FD js : size js = Bl.t - 1 =>
  0%r < mu Bl.FD.dt (fun (x : Bl.GP.exp) => ! (x \in js)).
  proof. 
    move => h. apply (AddDistr.mu_list _ _ Bl.GT.order). rewrite Bl.GP.ZModE.DZmodP.dunifinE.
    have : forall (a a' b b' : real), a <= a' => b = b' => 0%r < b => a / b <= a' / b'.
    move => a a' b b' h' h'' h'''. subst. elim h' => h'. left. smt(). smt(). move => h'. apply h'.
    move => @/DZmodP.Support.enum. clear h. elim js. smt(@List). move => x l ind_hyp. simplify.
    case (x \in l). smt(@List). move => g. have : (fun (x0 : exp) => ! (x0 = x \/ (x0 \in l))) =
    predI (fun x0 => x0 <> x)(fun x0 => (! x0 \in l)). smt(). move => h. rewrite h.
    rewrite countI. rewrite count_not_x. smt(@List). smt(@Bl.GP.ZModE). smt(@Bl.GT). smt(Bl.t_lt_card).
  qed.

(* The adversary cannot do better then randomly guessing an evaulation point *)
   lemma Hiding_Bound &m :
     islossless A_H.choose =>
     islossless A_H.guess =>   
  Pr[HidingSimp(A_H).rand() @ &m : res] <= (1%r/ Bl.GB.order%r).
proof.
  move => Ac_ll Ah_ll. byphoare. proc. inline *. seq 8 : true 1%r (1%r / Bl.GB.order%r) 0%r _ true. auto.
  conseq (_ : _ ==> _ : =1%r). call(_:true). auto. progress. smt(@Bl.FD). apply dpoly_ll. smt(@Bl.FD).
  if. swap [1..2] 5.  seq 5 : (size js = Bl.t - 1) 1%r (1%r / Bl.GB.order%r) 0%r _ true. auto. auto.
  (* case where the adversary casues themselves to lose *)
  case (i \in js). conseq (_ : _ ==> _ : =0%r). smt(@Bl.GB). seq 2 :  (i \in js) 1%r 0%r 0%r _ true. 
  auto. progress. hoare. auto. progress. rewrite H. trivial. hoare. auto. progress.
  (* other case *)
  conseq ( _ : _==> _ : = (1%r/Bl.GB.order%r)).  rnd. rnd. auto. progress. rewrite H. rewrite H0.  simplify.
  apply interpolate_prob2_dcond; trivial.
  (* js size flips *)
  conseq (_ : _ ==> _ : =0%r). auto. hoare. call(_:true). while (size js = Bl.t-1).  auto. progress. auto. progress.
  conseq (_ : _ ==> _ : =0%r). smt(@Bl.GB). hoare. auto. progress. smt(). auto. smt(). trivial. trivial.
qed.

lemma HidingSimp_Flip &m :
    islossless A_H.choose =>
     islossless A_H.guess =>   
    Pr[HidingSimp(A_H).real() @ &m : res] <= Pr[HidingSimp(A_H).rand() @ &m : res] .
proof.
  move => Ah_ll Ag_ll. byequiv. proc. inline*. seq 9 8 : (={glob A_H,a,pk1,b,pk2,key,m1,c,d,js}). 
  call(_:true). auto. progress. if. auto. call(:true). while(={glob A_H,j,ws,js,b,d,pk1} /\ (phiis_1{2}, phiis{2}) = phiis{1} /\
  0 <= j{1}). auto. progress. smt(). wp. seq 1 1 :( ={glob A_H, a, pk1, b, pk2, key, m1, c, d, js, js_1} /\ size js{1} = Bl.t - 1).
  auto. rnd : 0 0. auto. progress.  by rewrite -dprod_dlet dmap_id => />; case. rewrite -dprod_dlet. smt(@Distr). smt().
  auto. auto. auto.
qed.

lemma Hiding_comm_sim  &m :
    islossless A_H.guess =>
    islossless A_H.choose =>
    Pr[Hiding(PolyCommitPed,A_H).real() @ &m : res] <=  Pr[HidingSimp(A_H).comm_sim() @ &m : res  \/ HidingSimp.bad].
proof.
  move => Ag_ll Ac_ll. byequiv. proc. inline *. swap{1} [4..5] -3. swap{2} [3..4] -2. seq 1 1 : (={glob A_H, b}).
  rnd. auto. progress.

  (* Stupid case *)
  case (b{1} = zero). seq 15 14 : HidingSimp.bad{2}. while(={j} /\ HidingSimp.bad{2}). auto. progress. wp. rnd{2}. 
  call{1} (_:true==>true). call{2} (_ :true==> true). wp.  
  rnd{1}. rnd{2}. wp. rnd{2}. wp. rnd{1}. rnd{1}. auto. progress. apply dpoly_ll. smt(@Bl.FD).
  apply dpoly_ll. smt(@Bl.FD).  call{1} (_ :true==> true). auto.
  call{2} (_ :true==> true). auto. progress. rewrite H. auto. 
    
  (* resuming main *)
  call(_:true). while(={j,js,ws,key,phi,d}). auto. progress.
  swap{2} 9 -8. wp. call(_:true). wp.  rnd(fun m1 => phi{1} + (b{2} ** m1))(fun m1 => (inv b{2}) ** (m1-phi{1})). auto. 
  progress. smt(). smt(). smt(). smt(). smt().  rewrite scalepA. rewrite  Bl.GP.ZModE.ZModpRing.divrr.
  apply Bl.GP.ZModE.unitE; trivial. rewrite scale_1; trivial. smt(@IDPoly). rewrite size_mkseq.
  have: (max 0 (Bl.t + 1) - 1) = Bl.t. smt(Bl.t_valid). move => h. rewrite h. apply dpoly_uni. smt(Bl.t_valid). smt(@Bl.FD).
  apply dpoly_fu. smt(Bl.t_valid). smt(@Bl.FD). rewrite supp_dpoly in H5.  smt(Bl.t_valid). smt(@Bl.FD).
  apply dpoly_fu. smt(Bl.t_valid). smt(@Bl.FD). apply degZ_le_gen. apply degD_sim.  rewrite supp_dpoly in H5.  smt(Bl.t_valid). 
  smt().  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(degN).  apply dpoly_fu. smt(Bl.t_valid). smt(@Bl.FD). apply degD_sim.
  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(degN). apply degZ_le_gen. rewrite size_mkseq in H6. rewrite supp_dpoly in H6.
  smt(Bl.t_valid). smt(Bl.t_valid). have : phiL + b{2} ** m1L - phiL = b{2} ** m1L. smt(@IDPoly). move => h. rewrite h.
  rewrite scalepA. rewrite Bl.GP.ZModE.ZModpRing.mulrC. rewrite Bl.GP.ZModE.ZModpRing.divrr. apply Bl.GP.ZModE.unitE; trivial.
  rewrite scale_1; trivial. rewrite !head_mkKey !comPolEval.  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(@Bl.FD).
  rewrite size_mkseq in H6. rewrite supp_dpoly in H6.  smt(Bl.t_valid). smt(Bl.t_valid). apply degD_sim.
  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(). apply degZ_le_gen. rewrite size_mkseq in H6. rewrite supp_dpoly in H6.
  smt(Bl.t_valid). smt(Bl.t_valid). rewrite -Bl.GB.expM. rewrite Bl.exp_GB_asint_mul. rewrite -Bl.GB.expD.
  rewrite Bl.exp_GB_asint_add. rewrite -peval_add. rewrite -peval_mul. smt(@Bl.GP.ZModE).
  trivial. trivial. 
qed.

lemma dProd_size phiis :  phiis \in Bl.FD.dt `*` dlist Bl.FD.dt (Bl.t - 1) =>
    size phiis.`2 = Bl.t - 1.
proof.
  move => h. have : phiis.`2 \in  dlist Bl.FD.dt (Bl.t - 1). smt(@Distr). move => g. smt(@DList Bl.t_valid).
qed.
    
lemma Hiding_equiv &m :
    islossless A_H.guess =>
    islossless A_H.choose =>
     Pr[HidingSimp(A_H).comm_sim() @ &m : res \/ HidingSimp.bad] = Pr[HidingSimp(A_H).real() @ &m : res \/ HidingSimp.bad].
proof.
  move => Ag_ll Ac_ll. byequiv (_ : ={glob A_H} ==> (={res,HidingSimp.bad}) \/ (={HidingSimp.bad} /\ HidingSimp.bad{1})).
  proc. inline *. swap{1} [3..4] -2. swap{2} [3..4] -2. seq 1 1 : (={glob A_H, b}).
  rnd. auto. progress. 

    (* points and key equal *)
  seq 5 5 : (={glob A_H, b, key, pk1, pk2, a,HidingSimp.bad} /\ pk1{2} = key{2}.`1 /\
  key{2}.`1 = mkKey Bl.GB.g a{2}  /\ key{2}.`2 = mkKey(Bl.GB.g ^ asint b{2}) a{2} /\ HidingSimp.bad{1} = (b{1} = zero)).
  auto. progress.

  seq 3 3 : (={glob A_H, b, key, pk1, pk2, a, js,c,m1,HidingSimp.bad} /\ pk1{2} = key{2}.`1 /\ 
  key{2}.`1 = mkKey Bl.GB.g a{2}  /\ key{2}.`2 = mkKey(Bl.GB.g ^ asint b{2}) a{2} /\ d{2} = m1{2} /\ deg m1{1} <= Bl.t
   /\ HidingSimp.bad{1} = (b{1} = zero)). 
  call(_:true).  auto. progress. rewrite H. rewrite size_mkseq. smt(Bl.t_valid). rewrite H. rewrite size_mkseq. smt(Bl.t_valid).
  rewrite supp_dpoly in H2. smt(Bl.t_valid). smt().

  (* Stupid case *) 
  if{2}. case (b{1} = zero). seq 6 5  : (={HidingSimp.bad} /\ HidingSimp.bad{2}).
  while(={HidingSimp.bad,j} /\ HidingSimp.bad{2}). auto. progress. wp. rnd{2}. rnd{2}. rnd{1}. 
  auto. progress. apply dpoly_ll. smt(@Bl.FD). apply dcond_ll. apply mu_FD; trivial.
  call{1} (_ :true==> true). auto. call{2} (_ :true==> true). auto. progress. rewrite H. auto.

  (* second stupid case *)
  case (! uniq js{1}).  auto. call{1} (: true ==> true).  call{2} (: true ==> true).
  while(={j,js} /\ ! uniq js{1}). auto. progress.  auto. rnd{1}. rnd{2}.
  rnd{2}. auto. progress. apply dcond_ll. apply mu_FD; trivial. apply dpoly_ll. smt(@Bl.FD). smt().

  seq 3 2 : (={glob A_H, b, key, pk1, pk2, a, js,c,m1,HidingSimp.bad} /\ b{1} <> zero /\ pk1{2} = key{2}.`1 /\
  key{2}.`1 = mkKey Bl.GB.g a{2}  /\ key{2}.`2 = mkKey(Bl.GB.g ^ asint b{2}) a{2} /\ d{2} = m1{2} /\ phiis{1} = phiis{2}.`2
  /\ (phiis{2}.`1 :: phiis{2}.`2) = map (peval phi{1}) (js_1{2} :: js{2}) /\ deg phi{1} <= Bl.t /\ size js{2} = Bl.t - 1 /\
  d{1} = inv b{1} ** (m1{1} - phi{1})  /\ d{2} = m1{2} /\ deg m1{2} <= Bl.t /\ ! js_1{2} \in js{2} /\ uniq js{1} ).
  wp. rnd (fun x => (peval x js_1{2}, map (fun z => peval x z) js{1}))
(fun (y : exp * exp list ) => interpolate (js_1{2} :: js{1}) (y.`1 :: y.`2)). auto. progress. apply dcond_ll.
  apply mu_FD; trivial. rewrite interpolate_corr2_head; trivial. smt(@Distr). rewrite H2. rewrite eq_sym.
  apply dProd_size; trivial.  rewrite interpolate_corr2_tail; trivial. smt(@Distr). rewrite H2. rewrite eq_sym.
  apply dProd_size; trivial.  smt(). apply interpolate_prob. smt(@Distr).
  smt(@List). apply dProd_size; trivial. apply supp_dprod. split. smt(@Bl.FD). apply supp_dlist. smt(Bl.t_valid).
  split. smt(@List). apply allP.
  move => x1. move => h1. apply Bl.FD.dt_fu. rewrite eq_sym. apply interpolate_corr. smt(@List @BasePoly). smt(@List).
  smt(@Distr). smt(). rewrite supp_dpoly in H9. smt(Bl.t_valid). smt(). smt(@Distr). call(_:true).

  (* witness are equal *)
  while (={glob A_H,key,pk1,pk2,a,b,c,j,ws,js,m1} /\ deg phi{1} <= Bl.t  /\ b{1} <> zero /\
  key{2}.`1 = mkKey Bl.GB.g a{2} /\ phiis{2}.`2 =  phiis{1} /\
  (phiis{2}.`1 :: phiis{2}.`2) = map (peval phi{1}) (js_1{2} :: js{2}) /\ size js{1} = Bl.t -1 /\
  key{2}.`2 = mkKey(Bl.GB.g ^ asint b{2}) a{2}  /\ pk1{2} = key{2}.`1 /\ uniq js{1} /\
  d{2} = m1{2} /\ d{1} = inv b{2} ** (m1{1} - phi{1}) /\ deg m1{1} <= Bl.t  /\ 0 <= j{1} /\ ! js_1{2} \in js{2}).

  auto. progress.

  (* - witness exp is equal *) 
  rewrite -peval_mul -peval_add. rewrite H3. rewrite (nth_map zero). smt(). rewrite -peval_neg. trivial.

  (* - witness group is equal*)
  rewrite !H1 !H5. rewrite !head_mkKey !comPolEval; trivial. smt(degDiv). 
  apply (lez_trans (deg (inv b{2} ** (m1{2} - phi{1})))). apply degDiv. apply degZ_le_gen. apply degD_sim; trivial.
  rewrite degN; trivial. apply (lez_trans (deg m1{2})). apply degDiv; trivial. trivial. 
  rewrite -!Bl.GB.expM. rewrite -!Bl.GB.expD. apply Bl.exp_GB_can2. apply Bl.GP.pow_bij.
  rewrite !inzmodD !inzmodM !asintK. rewrite ediv_scale_1. apply Xi_neq_0. rewrite ediv_add_1.
    apply Xi_neq_0. rewrite ediv_neg_1. apply Xi_neq_0. rewrite -peval_mul. 
  have : b{2} * (peval ((edivpoly m1{2} (X - polyC (nth zero js{2} j{2}))).`1 -
    (edivpoly phi{1} (X - polyC (nth zero js{2} j{2}))).`1) a{2} * inv b{2}) =
      peval ((edivpoly m1{2} (X - polyC (nth zero js{2} j{2}))).`1 -
    (edivpoly phi{1} (X - polyC (nth zero js{2} j{2}))).`1) a{2}.
  rewrite -(Bl.GP.ZModE.ZModpField.mulrC (inv b{2})). rewrite Bl.GP.ZModE.ZModpField.mulrA. rewrite Bl.GP.ZModE.ZModpField.mulrV.
      trivial.  smt(@Bl.GP.ZModE.ZModpField). move => g. rewrite g. rewrite -peval_add -peval_neg. smt(@Bl.GP.ZModE.ZModpField).
  smt().
  (* closing *)
  auto. progress.  have : interpolate (js_1{2} :: js{2}) (phiis{2}.`1 :: phiis{2}.`2) = phi{1}. apply interpolate_corr.
  smt(@List). smt(@List). smt(@List).  rewrite H2 H3. smt(@List). move => h1. rewrite h1. left. smt(). 

  (* third stupid case *)
  auto. call{1} (: true ==> true). 
  while{1} (j{1} <= Bl.t -1) (Bl.t-j{1}-1). auto. progress. smt(). smt(). auto. progress. apply dpoly_ll.
  smt(@Bl.FD). smt(Bl.t_valid). smt(). smt(). trivial. smt().
qed.


lemma HidingSimp_real_split &m :
  Pr[HidingSimp(A_H).real() @ &m : res \/ HidingSimp.bad]
    <= Pr[HidingSimp(A_H).real() @ &m : res] + Pr[HidingSimp(A_H).real() @ &m : HidingSimp.bad].
  proof.
    byequiv. proc. seq 9 9 : (={glob A_H, HidingSimp.bad, js,c,d,b,pk1}). call(_:true). auto. if. smt(). call(_:true).
    while(={glob A_H, HidingSimp.bad, j,js,ws,c,d,b,phiis,pk1}). auto. progress. auto. progress. smt(). smt(). smt().
    auto. progress. smt(). smt(). smt(). smt(). auto.
  qed.

lemma HidingSimp_real_bad &m :
   islossless A_H.choose =>
   islossless A_H.guess => 
   Pr[HidingSimp(A_H).real() @ &m : HidingSimp.bad] + 1%r / Bl.GB.order%r = 2%r / Bl.GB.order%r.
proof.
  move => Ac_ll Ag_ll. have :Pr[HidingSimp(A_H).real() @ &m : HidingSimp.bad] = 1%r / Bl.GB.order%r =>
Pr[HidingSimp(A_H).real() @ &m : HidingSimp.bad] + 1%r / Bl.GB.order%r = 2%r / Bl.GB.order%r. smt().
  move => h. apply h. byphoare. proc.  seq 4 : HidingSimp.bad (1%r / Bl.GB.order%r) 1%r (1%r - (1%r / Bl.GB.order%r)) 0%r true;
  trivial. wp. rnd. wp. rnd. auto. progress. rewrite Bl.FD.dt1E. smt(Bl.order_eq). smt(@Bl.FD). seq 5 : HidingSimp.bad.
  auto. call( : HidingSimp.bad). auto.  progress. apply dpoly_ll. smt(@Bl). if.  call( : HidingSimp.bad).
  while ( HidingSimp.bad)(Bl.t-1-j). auto. progress. smt(). auto. progress. apply dcond_ll. apply mu_FD; trivial. apply dprod_ll.
  smt(@Bl @DList). smt(). auto. progress. 
  (* the failure event is not negated *)
  hoare. call( : HidingSimp.bad). auto. progress. hoare. seq 5 : (!HidingSimp.bad). call(_:true). auto. if.
  call(_:true). while (!HidingSimp.bad). auto. progress. auto. auto. trivial. trivial.
qed.

lemma PolyComDL2_Hiding  &m :
    islossless A_H.choose =>
    islossless A_H.guess => 
    Pr[Hiding(PolyCommitPed,A_H).real() @ &m : res] <= (2%r/ Bl.GB.order%r).
proof.
   move => Ac_ll Ag_ll. rewrite -(HidingSimp_real_bad &m); trivial.
   have : forall (b a c : real), a <= b => b <= c => a <= c. smt(). move=> h'.  
  apply (h' Pr[HidingSimp(A_H).real() @ &m : res \/ HidingSimp.bad]). rewrite -Hiding_equiv; trivial.
  apply Hiding_comm_sim; trivial.
  have : forall (a b c d : real), d <= c => a <= b + d => a <= b + c. smt(). move => h''.
  apply (h'' _ _ _ (Pr[HidingSimp(A_H).real() @ &m : res])). apply (h' Pr[HidingSimp(A_H).rand() @ &m : res]).
  apply HidingSimp_Flip; trivial. apply  Hiding_Bound; trivial.  smt(HidingSimp_real_split).
qed.

(*******************)
(** Strong hiding **)
(*******************) 

op key_valid (g ga : Bl.GB.group, x : Bl.GB.group list)(i : int) : bool = Bl.e g (nth Bl.GB.g x (i+1)) = Bl.e ga (nth Bl.GB.g x i).

module PolyCommitPed_A : PC_Algorithms = {
  proc valid_key(key : (Bl.GB.group) list * (Bl.GB.group) list) = {
    var g, ga, h,  b, b';
    g <- Bl.GB.g;
    ga <- nth Bl.GB.g key.`1 1;
    h <- head Bl.GB.g key.`2;
    
    b <- all (key_valid g ga key.`1) (range 0 Bl.t);
    b' <- all (key_valid g ga key.`2) (range 0 Bl.t);
    return size key.`1 = Bl.t + 1 /\ size key.`2 = Bl.t + 1 /\ b /\ b' /\ ga <> Bl.GB.e /\ h <> Bl.GB.e;
  }

  proc extract(key : (Bl.GB.group) list * (Bl.GB.group) list) : exp * exp= {
    var g, ga, h, i, j, found;
    g <- Bl.GB.g;
    ga <- nth Bl.GB.g key.`1 1;
    h <- head Bl.GB.g key.`2;
    
    found <- false;
    i <- 0;
    while(i < Bl.GB.order /\ !found){
      if (h = g ^ i){found <- true;}
      i<-i+1; 
    }

    found <- false;
    j <- 0;
    while(j < Bl.GB.order /\ !found){
      if (ga = g ^ j){found <- true;}
      j<-j+1;
    }
    
    return (inzmod (i -1), inzmod (j-1)); 
  }
}.

(* Some addational list lemmas *)

lemma eq_from_nth_ind (a : 'a) (s1 s2 : 'a list):
    size s1 = size s2 =>
    (fun i => nth a s1 i = nth a s2 i) 0
  => (forall i, 0 <= i => (fun j => nth a s1 j = nth a s2 j) i => (fun j => nth a s1 j = nth a s2 j) (i + 1))
  => s1 = s2.
proof.                        
  move => h_size h0 h_ind. have : (forall i, 0 <= i => (fun (j : int) => nth a s1 j = nth a s2 j) i) => s1 = s2. smt(@List).
  move => g. apply g. apply intind; trivial.
qed.

lemma nth_from_all_key_valid i g ga x:
    all (key_valid g ga x) (range 0 Bl.t) =>
     0 <= i < Bl.t =>
     Bl.e g (nth Bl.GB.g x (i+1)) = Bl.e ga(nth Bl.GB.g x i).
proof.
  move => hi h_all. have: key_valid g ga x i. smt(@List). move => h'. rewrite h'. trivial.
qed.

lemma nth_from_all_key_valid_ind i g j x:
    g <> Bl.GB.e =>
    all (key_valid g (g^j) x) (range 0 Bl.t) =>
    0 <= i < Bl.t =>
    nth Bl.GB.g x i = g ^ asint (exp (inzmod j) i) =>
    nth Bl.GB.g x (i+1) = g ^ asint (exp (inzmod j) (i+1)).
proof.
  move => g_neq_e h_all hi h_ind. have: key_valid g (g^j) x i. smt(@List). move => @/key_valid. move => h'.
  rewrite h_ind in h'. rewrite Bl.e_pow1 in h'. rewrite -Bl.e_pow2 in h'.
  have : nth Bl.GB.g x (i + 1) = g ^ asint (exp (inzmod j) i) ^ j. apply (Bl.e_inj1 _ _ g); trivial. smt(@Bl).
move => h. rewrite h. rewrite !exp_inzmod. elim hi => hi hi'. rewrite hi. have : 0 <= i + 1. smt(). move => hii. rewrite hii.
  simplify. rewrite !inzmodK. rewrite -Bl.order_eq. rewrite !Bl.exp_g_modz. rewrite -Bl.GB.expM. rewrite exprS. smt(). smt().
qed.

(* resuming *)

lemma valid_key_extract_corr (key : (Bl.GB.group) list * (Bl.GB.group) list) i j :
  (* The discrete logs we extracted *)
  head Bl.GB.g key.`2 = Bl.GB.g ^ i =>
  nth Bl.GB.g key.`1 1 = Bl.GB.g ^ j =>
  (* Basic length checks *)   
  size key.`1 = Bl.t +1 =>
  size key.`2 = Bl.t +1 =>
  Bl.GB.g ^ j <> Bl.GB.e =>
  Bl.GB.g ^ i <> Bl.GB.e =>  
  (* The main check *)
  all (key_valid Bl.GB.g (nth Bl.GB.g key.`1 1) key.`1) (range 0 Bl.t) =>
  all (key_valid Bl.GB.g (nth Bl.GB.g key.`1 1) key.`2) (range 0 Bl.t) =>
    
  key = (mkKey Bl.GB.g (inzmod j), mkKey (Bl.GB.g ^ asint (inzmod i)) (inzmod j)).
proof.
  move => hi hj sk1 sk2 ga_neq0 ha_neq0 all1 all2. rewrite hj in all1. rewrite hj in all2. rewrite pairS. apply pw_eq.

  (* left half of key correct *)
  apply (eq_from_nth_ind Bl.GB.g). rewrite size_mkseq. smt(@Bl).
  (* base case *)
  simplify. rewrite nth_mkseq. smt(@Bl). simplify. apply (nth_from_all_key_valid 0) in all1. rewrite hj in all1.
  rewrite (Bl.e_comm _ (nth Bl.GB.g key.`1 0)) in all1. apply (Bl.e_inj1 _ _  (Bl.GB.g ^ j)); trivial. smt(@Bl).
  (* ind case *)
  simplify. move => i0 hi0. case (i0 < Bl.t) => h hind.  rewrite nth_mkseq. smt(). simplify.
  apply nth_from_all_key_valid_ind; trivial. apply Bl.g_neq_e. smt(@List). rewrite !nth_default. smt(). rewrite size_mkseq.
  smt(Bl.t_valid). trivial.

  (* right half of key correct*)
  apply (eq_from_nth_ind Bl.GB.g). rewrite size_mkseq. smt(@Bl).

  (* base case *)
  simplify. rewrite nth_mkseq. smt(@Bl). simplify. rewrite nth0_head. rewrite hi. smt(@Bl).
  (* ind case *)
  simplify. move => i0 hi0. case (i0 < Bl.t) => h hind. rewrite nth_mkseq. smt(). simplify.
  apply (nth_from_all_key_valid i0) in all2. rewrite Bl.e_pow1 in all2. rewrite -Bl.e_pow2 in all2.
  rewrite Bl.e_comm in all2. rewrite (Bl.e_comm Bl.GB.g) in all2. apply (Bl.e_inj1 _ _  Bl.GB.g); trivial.
  apply Bl.g_neq_e. rewrite hind in all2. rewrite all2. smt(). rewrite nth_mkseq. smt(). simplify. congr.
  rewrite -Bl.GB.expM. rewrite !exp_inzmod. rewrite hi0. have : 0 <= i0 + 1. smt(). move => hii. rewrite hii.
  simplify. rewrite -!Bl.GB.expM. rewrite !(mulrC (asint (inzmod i))). rewrite !Bl.GB.expM. congr.
  rewrite !inzmodK. rewrite -Bl.order_eq. rewrite !Bl.exp_g_modz. rewrite exprS. smt(). rewrite Bl.GB.expM. smt(@Bl.GB).
  (* Case where i0 is beyond the list *)
  rewrite !nth_default. smt(). rewrite size_mkseq. smt(Bl.t_valid). trivial.
qed.

module Setup_valid_key = {
  proc main() = {
    var ck, b;
    ck <@ PolyCommitPed.setup();
    b  <@ PolyCommitPed_A.valid_key(ck);
    return b;
  }
}.

lemma PolyCom_Setup_correct &m :
  Pr[Setup_valid_key.main() @ &m : res] = (1%r - (1%r / Bl.GB.order%r)) ^ 2.
proof.
  byphoare. proc. inline *. swap 2 1.
  seq 2 : (b0 <> zero /\ a <>  zero) ((1%r- (1%r / Bl.GB.order%r))^2) 1%r (1%r- (1%r- (1%r / Bl.GB.order%r))^2)  0%r true; trivial.
  seq 1 : (a <> zero) (1%r- (1%r / Bl.GB.order%r)) (1%r-(1%r/Bl.GB.order%r)) ((1%r / Bl.GB.order%r)^2)  0%r true; trivial.
  rnd. auto. progress.  rewrite Bl.FD_nin. smt(Bl.order_eq). rnd. auto. progress. rewrite H.  simplify. rewrite Bl.FD_nin.
  trivial. rnd. auto.  progress. smt(@Distr). smt(@Int).

  (* Given a and b0 are non-zero *)
  auto. progress. 
  (* keys of correct length *)
  smt(@List Bl.t_valid). smt(@List Bl.t_valid).
  (* first part valid *)
  apply (all_nthP _ _ 0). move => i hi. move => @/key_valid. rewrite mkKey_ga. 
  rewrite nth_mkseq. smt(@List Bl.t_valid). rewrite nth_mkseq. smt(@List Bl.t_valid). simplify.
  rewrite Bl.e_pow. rewrite Bl.e_pow2. rewrite Bl.e_g_g. rewrite Bl.exp_GT_asint_mul. congr.
  congr. rewrite nth_range. smt(@List Bl.t_valid). smt(@Bl).
  (* second part valid *)
  apply (all_nthP _ _ 0). move => i hi. move => @/key_valid. rewrite mkKey_ga. 
  rewrite nth_mkseq. smt(@List Bl.t_valid). rewrite nth_mkseq. smt(@List Bl.t_valid). simplify.
  rewrite nth_range. smt(@List Bl.t_valid).
  rewrite !Bl.e_pow. rewrite !Bl.e_pow2. rewrite Bl.e_g_g. rewrite !Bl.GT.expM. 
  rewrite eq_sym. rewrite -Bl.GT.expM. rewrite Bl.exp_GT_asint_mul. congr.  smt(@Bl).
  (* are generators *)
  rewrite nth_mkseq. smt(Bl.t_valid). simplify. smt(@Bl). 
  rewrite head_mkKey. smt(@Bl).
  (* dumb parts *)
  hoare. auto. progress. rewrite head_mkKey.  rewrite nth_mkseq. smt(Bl.t_valid). simplify. smt(@Bl). trivial. trivial.
 qed.
 

 module HidingSimpS (A : AdvSH) = {
     
    var bad : bool

     (* first we move to this game *)
   proc comm_sim() : bool = {
     var key; (* The polynomial and commitment scheme key *)
      var c : Bl.GB.group; (* Commitment to the polynoimal *)
      var i, phii : exp; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis;
      var ws : (exp * Bl.GB.group) list; (* witness to evaluation *)
      var  phi;
      var j : int;
      var a, b, b', m1, phi0, phi1, psi, psi1, w, temp1, temp2;                
      key <@ A.setup();

     
     (b,a) <@ PolyCommitPed_A.extract(key);
     b' <@ PolyCommitPed_A.valid_key(key);
      m1 <$ dpoly Bl.t Bl.FD.dt;                
     c <- prodEx (head Bl.GB.g key.`1) key.`1 m1;                                                                               
     js <@ A.choose(c);
         phi <$ dpoly Bl.t Bl.FD.dt;
     d <- ((inv b) ** (m1  - phi));
     phiis <- map  (fun (x1 : Bl.GP.exp) => peval phi x1) js;
       ws <- [];                                                      
       j <- 0;                                             
       while (j < Bl.t - 1) {                                                                 
       i <- nth zero js j;                                                                 
       phi0 <- peval phi i;                                                                
       phi1 <- peval d i;                                                           
       psi <- (edivpoly phi (X - polyC i)).`1;                                        
       psi1 <- (edivpoly d (X - polyC i)).`1;                                              
       w <- Bl.GB.( * )                                                                                 
       (prodEx (head Bl.GB.g key.`1) key.`1                                               
         psi)                                                                         
        ( prodEx (head Bl.GB.g key.`2) key.`2                                               
         psi1);                                                                    
       (temp1, temp2) <- (phi0, (phi1, w));                                            
         ws <- temp2 :: ws;                                                             
         j <- j + 1;                                                                         
     }                                                                                    
     (i, phii) <@ A.guess(phiis, ws);
     return b' /\ phii = peval phi i /\ !(i \in js) /\ size js = Bl.t - 1  /\ uniq js;
    }
   
   
    proc real() : bool = {
      var key; (* The polynomial and commitment scheme key *)
      var c : Bl.GB.group; (* Commitment to the polynoimal *)
      var i, phii : exp; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis : (exp * exp list); (* eval at the points in js *)
      var ws : (exp * Bl.GB.group) list; (* witness to evaluation *)
      var temp2, js_1;
      var j : int;
      var m1, b, b', a;
     
      key <@ A.setup();
      b' <@ PolyCommitPed_A.valid_key(key);
     
      (b,a) <@ PolyCommitPed_A.extract(key);
      m1 <$ dpoly (size key.`1 - 1)  Bl.FD.dt;                
      (c, d) <- ((prodEx (head Bl.GB.g key.`1) key.`1 m1)%Bl.GB, m1);

      (* construct evaluation points *)
      js <@ A.choose(c);

      if (size js = Bl.t -1) {
        js_1 <$  dcond  Bl.FD.dt (fun x => ! x \in js);
        phiis <$ Bl.FD.dt `*` dlist Bl.FD.dt (Bl.t-1);
        
        ws <- [];
        j <- 0;
        while (j < Bl.t -1) {
        temp2 <- ((peval d (nth zero js j)  - (nth zero phiis.`2 j)) / b,
        prodEx (head Bl.GB.g key.`1) key.`1 (edivpoly d (X - polyC (nth zero js j))).`1);
        ws <- temp2 :: ws;
        j <- j +1;
        }  
        
        (i, phii) <@ A.guess(phiis.`2,ws);
      } else {
        js_1 <- zero;
        i <- zero;
        phii <- zero;
        phiis <- (zero,[]);
      }

      return b' /\ (phii = peval (interpolate (js_1 :: js) (phiis.`1 :: phiis.`2))  i) /\
          !(i \in js) /\ size js = Bl.t-1  /\ uniq js;
    }

    proc rand() : bool = {
      var key; (* The polynomial and commitment scheme key *)
      var c : Bl.GB.group; (* Commitment to the polynoimal *)
      var i, phii : exp; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis : exp list; (* eval at the points in js *)
      var ws : (exp * Bl.GB.group) list; (* witness to evaluation *)
      var temp2,  js_1, phiis_1;
      var j : int;
      var m1, b, a;
     
      key <@ A.setup();
      
      (b,a) <@ PolyCommitPed_A.extract(key);
      m1 <$ dpoly (size key.`1 - 1)  Bl.FD.dt;                
      (c, d) <- ((prodEx (head Bl.GB.g key.`1) key.`1 m1)%Bl.GB, m1);

      (* construct evaluation points *)
      js <@ A.choose(c);

      
      if (size js = Bl.t -1) {
        js_1 <$  dcond  Bl.FD.dt (fun x => ! x \in js);
        phiis_1 <$ Bl.FD.dt;
        phiis   <$  dlist Bl.FD.dt (Bl.t-1);

        ws <- [];
        j <- 0;
        while (j < Bl.t -1) {
        temp2 <- ((peval d (nth zero js j)  - (nth zero phiis j)) / b,
        prodEx (head Bl.GB.g key.`1) key.`1 (edivpoly d (X - polyC (nth zero js j))).`1);
        ws <- temp2 :: ws;
        j <- j +1;
        }  
        
        (i, phii) <@ A.guess(phiis,ws);
      } else {
        i <- zero;
        js_1 <- zero;
        phii <- zero;
        phiis <- [];
        phiis_1 <- zero;
      }

      return (phii = peval (interpolate (js_1 :: js) (phiis_1 :: phiis))  i) /\ !(i \in js) /\ size js = Bl.t-1;
    }
  }.

 declare module A_SH <: AdvSH.

(* The adversary cannot do better then randomly guessing an evaulation point *)
lemma Hiding_BoundS &m :
    islossless A_SH.setup =>
    islossless A_SH.choose =>
     islossless A_SH.guess =>
    Pr[HidingSimpS(A_SH).rand() @ &m : res] <= (1%r/ Bl.GB.order%r).
proof.
  move => As_ll Ac_ll Ag_ll. byphoare. proc. inline *. seq 15 : true 1%r (1%r / Bl.GB.order%r) 0%r _ true. auto.
  conseq (_ : _ ==> _ : =1%r). call(_:true). auto. while (true)(Bl.GB.order-j0). progress. auto. progress. smt().
  wp. while (true)(Bl.GB.order-i0). progress. auto. progress. smt(). auto. call(_:true). auto. progress. smt(). smt().
  apply dpoly_ll. smt(@Bl.FD). 

  if. swap [1..2] 5.  seq 5 : (size js = Bl.t - 1) 1%r (1%r / Bl.GB.order%r) 0%r _ true. auto. auto.
  (* case where the adversary casues themselves to lose *)
  case (i \in js). conseq (_ : _ ==> _ : =0%r). smt(@Bl.GB). seq 2 :  (i \in js) 1%r 0%r 0%r _ true. 
  auto. progress. hoare. auto. progress. rewrite H. trivial. hoare. auto. progress.
  (* other case *)
  conseq ( _ : _==> _ : = (1%r/Bl.GB.order%r)).  rnd. rnd. auto. progress. rewrite H. rewrite H0.  simplify.
  apply interpolate_prob2_dcond; trivial.
  (* js size flips *)
  conseq (_ : _ ==> _ : =0%r). auto. hoare. call(_:true). while (size js = Bl.t-1).  auto. progress. auto. progress.
  conseq (_ : _ ==> _ : =0%r). smt(@Bl.GB). hoare. auto. progress. smt(). auto. smt(). trivial. trivial.
qed.

lemma HidingSimp_FlipS &m :
    islossless A_SH.setup =>
     islossless A_SH.guess =>
    Pr[HidingSimpS(A_SH).real() @ &m : res] <=  Pr[HidingSimpS(A_SH).rand() @ &m : res].
proof.
  move => As_ll Ag_ll. byequiv. proc. inline *. seq 22 15 : (={glob A_SH, js,b,c,d,key}). call(:true). auto.
  while (={glob A_SH,key,g,h,i0,j0,found} /\ 0 <= j0{1} /\ ga0{1} = ga{2} /\ g0{1} = g{2}). auto. progress. smt(). smt(). auto.
  while (={glob A_SH,key,g,h,i0,found} /\ 0 <= i0{1} /\ ga0{1} = ga{2} /\ g0{1} = g{2} /\ h0{1} = h{2}). auto. progress.
  smt(). smt(). auto. call(_:true). auto. progress. if. smt().
  (* main line *)
  call(_:true).  while(={glob A_SH,j,ws,js,b,d,key} /\ (phiis_1{2}, phiis{2}) = phiis{1} /\ 0 <= j{2}). auto. progress. smt(). wp.
  seq 1 1 : (={glob A_SH,js,js_1,b,c,d,key}). auto.  rnd : 0 0. auto. progress.
  by rewrite -dprod_dlet dmap_id => />; case. rewrite -dprod_dlet. smt(@Distr). smt(). 
  (* final stupid case*) 
  auto. progress. auto. 
qed.

lemma SHiding_equiv1 &m :
    islossless A_SH.setup =>
    islossless A_SH.choose =>
    islossless A_SH.guess =>
     Pr[Strong_Hiding(PolyCommitPed,PolyCommitPed_A,A_SH).real() @ &m : res] <= Pr[HidingSimpS(A_SH).comm_sim() @ &m : res].
proof.
  move => As_ll Ac_ll Ag_ll. byequiv. proc. swap{1} 1 2. seq 1 1 : (={glob A_SH, key}). call (_:true). auto.

  (* discharge case of invalid key *)
  swap{2} 1 1. 
  seq 1 1 : (={glob A_SH, key} /\ b{1} = b'{2} /\ (!b{1} \/
    (all (key_valid Bl.GB.g (nth Bl.GB.g key{1}.`1 1) key{1}.`1) (range 0 Bl.t) /\
      all (key_valid Bl.GB.g (nth Bl.GB.g key{1}.`1 1) key{1}.`2) (range 0 Bl.t) /\
      size key{1}.`1 = Bl.t + 1 /\ size key{1}.`2 = Bl.t + 1 /\ head Bl.GB.g key{1}.`2 <> Bl.GB.e /\
      nth Bl.GB.g key{1}.`1 1 <> Bl.GB.e))).
  inline *. auto. progress. smt(). case(!b{1}). call{1} (_ :true==> true). 
      call{2} (_ :true==> true).  while(={j} /\ !b{1}). inline *. auto. inline *. auto. call{1} (_: true ==> true).
      call{2} (_: true ==> true). wp. rnd{2}. rnd{1}. wp.  while{2} (true) (Bl.GB.order-j0{2}). auto. progress. smt(). wp.
  while{2} (true) (Bl.GB.order-i0{2}). auto. progress. smt(). auto. progress. apply dpoly_ll.
      apply coeff_sample_ll. smt(). smt(). apply dpoly_ll. apply Bl.FD.dt_ll. smt(). smt(). smt(). smt().

  (* showing that extraction is valid *)
  seq 0 1 : (={glob A_SH, key} /\ b{1} = b'{2} /\ key{1} = (mkKey Bl.GB.g a{2}, mkKey (Bl.GB.g ^  asint b{2}) a{2}) /\
      b{2} <> zero). inline *. wp.
  (* either we have found the discrete log of ga or all the valus we tried didn't work AND
     either we aren't done trying all options or we found the discrete log *)
  while{2} (g{2} = Bl.GB.g /\ (found{2} \/ forall j, 0 <= j < j0{2} => ga{2} <> g{2} ^ j) /\
  (found{2} => ga{2} = g{2} ^ (j0{2} - 1)) /\ (j0{2} < Bl.GB.order \/ ga{2} = g{2} ^ (j0{2} - 1))) (Bl.GB.order - j0{2}).
    auto. progress.
  smt(). smt().
  (* We didn't find the answer so there must be more space*)
  case (j0{hr} = Bl.GB.order - 1) => h. elim (Bl.GB.log_spec ga{hr}) => k hk. elim hk => hk hk'. subst. smt().
      smt(). smt(). wp.
  while{2} (g{2} = Bl.GB.g /\ (found{2} \/ forall j, 0 <= j < i0{2} => h{2} <> g{2} ^ j) /\ (found{2} => h{2} = g{2} ^ (i0{2} - 1))
      /\ (i0{2} < Bl.GB.order \/ h{2} = g{2} ^ (i0{2} - 1))) (Bl.GB.order - i0{2}). auto. progress.
  smt(). smt().
  (* We didn't find the answer so there must be more space*)
  case (i0{hr} = Bl.GB.order - 1) => h. elim (Bl.GB.log_spec h{hr}) => k hk. elim hk => hk hk'. subst. smt().
      smt(). smt(). wp. auto. progress.

  (* various silly cases *) 
    smt(). smt(@Bl). smt(@Bl). smt(@Bl). smt(@Bl). smt(@Bl).

    (* cleaning invariants *)
  clear H2 H6. rewrite negb_and in H1. rewrite negb_and in H5. elim H => H. smt(). 
  have : head Bl.GB.g key{2}.`2 = Bl.GB.g ^ (i0_R - 1). smt(). move => h.
  have :  nth Bl.GB.g key{2}.`1 1 = Bl.GB.g ^ (j0_R - 1). smt(). move => h'. clear H8 H7 H5 H4 H3 H1. elim H => H [H' H''].

   (* key correct*)
  apply valid_key_extract_corr; trivial. smt(). smt(). smt(). smt(). 

  (* h not the generator *)
   have : head Bl.GB.g key{2}.`2 = Bl.GB.g ^ (i0_R - 1). smt(). move => h. elim H => H. smt(). elim H => H [H' H''].
    rewrite  h in H''. smt(@Bl).

  (* resuming main *)
  call(_:true). inline *.  while(={j,js,ws,key,phi,d}). auto. progress. wp. swap{2} 4 -3. call(_:true). wp.
  rnd(fun m1 => phi{1} + (b{2} ** m1))(fun m1 => (inv b{2}) ** (m1-phi{1})). auto. 
  progress. rewrite scalepA. rewrite  Bl.GP.ZModE.ZModpRing.divrr.
  apply Bl.GP.ZModE.unitE; trivial. rewrite scale_1; trivial. smt(@IDPoly). rewrite size_mkseq.
  have: (max 0 (Bl.t + 1) - 1) = Bl.t. smt(Bl.t_valid). move => h. rewrite h. apply dpoly_uni. smt(Bl.t_valid). smt(@Bl.FD).
  apply dpoly_fu. smt(Bl.t_valid). smt(@Bl.FD). rewrite supp_dpoly in H3.  smt(Bl.t_valid). smt(@Bl.FD).
  apply dpoly_fu. smt(Bl.t_valid). smt(@Bl.FD). apply degZ_le_gen. apply degD_sim.  rewrite supp_dpoly in H3.  smt(Bl.t_valid). 
  smt().  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(degN).  apply dpoly_fu. smt(Bl.t_valid). smt(@Bl.FD). apply degD_sim.
  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(degN). apply degZ_le_gen. rewrite size_mkseq in H4. rewrite supp_dpoly in H4.
  smt(Bl.t_valid). smt(Bl.t_valid). have : phiL + b{2} ** m1L - phiL = b{2} ** m1L. smt(@IDPoly). move => h. rewrite h.
  rewrite scalepA. rewrite Bl.GP.ZModE.ZModpRing.mulrC. rewrite Bl.GP.ZModE.ZModpRing.divrr. apply Bl.GP.ZModE.unitE; trivial.
  rewrite scale_1; trivial. rewrite !head_mkKey !comPolEval.  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(@Bl.FD).
  rewrite size_mkseq in H4. rewrite supp_dpoly in H4.  smt(Bl.t_valid). smt(Bl.t_valid). apply degD_sim.
  rewrite supp_dpoly in H0.  smt(Bl.t_valid). smt(). apply degZ_le_gen. rewrite size_mkseq in H4. rewrite supp_dpoly in H4.
  smt(Bl.t_valid). smt(Bl.t_valid). rewrite -Bl.GB.expM. rewrite Bl.exp_GB_asint_mul. rewrite -Bl.GB.expD.
  rewrite Bl.exp_GB_asint_add. rewrite -peval_add. rewrite -peval_mul. smt(@Bl.GP.ZModE).
  trivial. trivial. 
qed.     


lemma SHiding_equiv2 &m :
    islossless A_SH.setup =>
    islossless A_SH.choose =>
    islossless A_SH.guess =>
    Pr[HidingSimpS(A_SH).real() @ &m : res] = Pr[HidingSimpS(A_SH).comm_sim()  @ &m : res].
proof.
  move => As_ll Ac_ll Ag_ll. byequiv. proc.

  seq 1 1 : (={glob A_SH, key}). call(_ : true). auto. progress.

   (* discharge case of invalid key *)
  swap{2} 1 1. 
  seq 1 1 : (={glob A_SH, key, b'} /\ (!b'{1} \/
    (all (key_valid Bl.GB.g (nth Bl.GB.g key{1}.`1 1) key{1}.`1) (range 0 Bl.t) /\
      all (key_valid Bl.GB.g (nth Bl.GB.g key{1}.`1 1) key{1}.`2) (range 0 Bl.t) /\
      size key{1}.`1 = Bl.t + 1 /\ size key{1}.`2 = Bl.t + 1 /\ head Bl.GB.g key{1}.`2 <> Bl.GB.e /\
      nth Bl.GB.g key{1}.`1 1 <> Bl.GB.e))).
      inline *. auto. progress.  smt(). case(!b'{1}). wp.
      call{2} (_ :true==> true). seq 4 4 : (={b'} /\ !b'{1}). call{1}(_:true==>true). call{2}(_:true==>true).
      wp. rnd{1}. rnd{2}. inline *. wp. 
   while{2} (true) (Bl.GB.order-j0{2}). auto. progress. smt(). wp.
      while{2} (true) (Bl.GB.order-i0{2}). auto. progress. smt().
  while{1} (true) (Bl.GB.order-j0{1}). auto. progress. smt(). wp.
      while{1} (true) (Bl.GB.order-i0{1}). auto. progress. smt(). wp. auto. progress. smt(). smt(). smt(). smt(). 
      apply dpoly_ll. apply Bl.FD.dt_ll.  apply dpoly_ll. apply Bl.FD.dt_ll.  if{1}. call{1} (_ :true==> true).
     while(={j} /\ !b'{1}). auto. auto. rnd{1}. rnd{2}. rnd{1}. auto. progress. apply dcond_ll. apply mu_FD; trivial.
      apply dpoly_ll. smt(@Bl.FD). smt(). while{2} (true) (Bl.GB.order-j{2}). auto. progress. smt(). auto.
    progress.  apply dpoly_ll. smt(@Bl.FD). smt(@Bl). smt().

  (* showing that extraction is valid *)
  seq 1 1 : (={glob A_SH, key, b', b, a} /\ b'{1} /\ key{1} = (mkKey Bl.GB.g a{2}, mkKey (Bl.GB.g ^  asint b{2}) a{2}) /\
      b{2} <> zero). inline *. wp.
  (* either we have found the discrete log of ga or all the valus we tried didn't work AND
     either we aren't done trying all options or we found the discrete log *)
  while (={found,ga, g, j0} /\ g{2} = Bl.GB.g /\ (found{2} \/ forall j, 0 <= j < j0{2} => ga{2} <> g{2} ^ j) /\
  (found{2} => ga{2} = g{2} ^ (j0{2} - 1)) /\ (j0{2} < Bl.GB.order \/ ga{2} = g{2} ^ (j0{2} - 1))).
    auto. progress. smt(). 
  (* We didn't find the answer so there must be more space*)
  case (j0{2} = Bl.GB.order - 1) => h. elim (Bl.GB.log_spec ga{2}) => k hk. elim hk => hk hk'. subst. smt().
      smt().  wp.
  while (={found, h, g, i0} /\ g{2} = Bl.GB.g /\ (found{2} \/ forall j, 0 <= j < i0{2} => h{2} <> g{2} ^ j) /\
  (found{2} => h{2} = g{2} ^ (i0{2} - 1))  /\ (i0{2} < Bl.GB.order \/ h{2} = g{2} ^ (i0{2} - 1))). auto. progress.
  smt().
  (* We didn't find the answer so there must be more space*)
  case (i0{2} = Bl.GB.order - 1) => h. elim (Bl.GB.log_spec h{2}) => k hk. elim hk => hk hk'. subst. smt().
    smt(). auto. progress.

  (* various silly cases *) 
    smt(). smt(@Bl). smt(@Bl). smt(@Bl). 

    (* cleaning invariants *)
  clear H2 H6. rewrite negb_and in H1. rewrite negb_and in H7. elim H => H. smt(). 
  have : head Bl.GB.g key{2}.`2 = Bl.GB.g ^ (i0_R - 1). smt(). move => h.
  have :  nth Bl.GB.g key{2}.`1 1 = Bl.GB.g ^ (j0_R - 1). smt(). move => h'. clear H8 H7 H5 H4 H3 H1. elim H => H [H' H''].

   (* key correct*)
  apply valid_key_extract_corr; trivial. smt(). smt(). smt(). smt(). 

  (* h not the generator *)
   have : head Bl.GB.g key{2}.`2 = Bl.GB.g ^ (i0_R - 1). smt(). move => h. elim H => H. smt(). elim H => H [H' H''].
    rewrite  h in H''. smt(@Bl).

  (* points and commit equal *)
    seq 3 3 : (={glob A_SH, b', b, a, key, m1, c, js} /\ d{1}=m1{1} /\ b{2} <> zero /\
     key{1} = (mkKey Bl.GB.g a{2}, mkKey (Bl.GB.g ^  asint b{2}) a{2}) /\ deg m1{2} <= Bl.t). call(_:true). auto. progress.
    rewrite size_mkseq. smt(Bl.t_valid). rewrite size_mkseq in H2. smt(Bl.t_valid).
    rewrite size_mkseq in H2. smt(Bl.t_valid @BasePoly).

  (* second stupid case*)
  if{1}; last first. auto. call{2} (: true ==> true). 
    while{2} true (Bl.t -j{2}). auto. progress. smt(). wp. rnd{2}.
    auto. progress. apply dpoly_ll. smt(@Bl.FD). smt(). smt().

  case (uniq js{1}).  seq 2 3: (={glob A_SH, b, key, a,b,b', js,c,m1} /\ b{1} <> zero /\ 
  key{2}.`1 = mkKey Bl.GB.g a{2}  /\ key{2}.`2 = mkKey(Bl.GB.g ^ asint b{2}) a{2} /\ d{1} = m1{1} /\ phiis{2} = phiis{1}.`2
  /\ (phiis{1}.`1 :: phiis{1}.`2) = map (peval phi{2}) (js_1{1} :: js{2}) /\ deg phi{2} <= Bl.t /\ size js{2} = Bl.t - 1 /\
  d{2} = inv b{2} ** (m1{2} - phi{2})  /\ d{1} = m1{1} /\ deg m1{2} <= Bl.t  /\ uniq (js_1{1} :: js{1})).
    wp. rnd (fun (y : exp * exp list ) => interpolate (js_1{1} :: js{1}) (y.`1 :: y.`2))
  (fun x => (peval x js_1{1}, map (fun z => peval x z) js{1})). auto. progress.
  apply dcond_ll. apply mu_FD;trivial. rewrite eq_sym. apply interpolate_corr; trivial. smt(@List @BasePoly). smt(@List).
  smt(@Distr). rewrite H5. trivial. rewrite eq_sym. pose y := mu1 (dpoly Bl.t Bl.FD.dt)
  (interpolate (js_10 :: js{2}) (peval phiR js_10 :: map (peval phiR) js{2})). rewrite -H5. trivial. move => @/y.
    apply interpolate_prob. smt(@Distr). smt(@List). smt(@List). apply interpolate_in_dpoly. smt(@List).
    apply dProd_size in H7. smt(@List). rewrite interpolate_corr2_head; trivial. smt(@Distr). rewrite H1. rewrite eq_sym.
    apply dProd_size; trivial. rewrite interpolate_corr2_tail; trivial. smt(@Distr). rewrite H1. rewrite eq_sym.
    apply dProd_size; trivial. smt(). smt(). smt(). smt(). smt(interpolate_deg @List). smt(@Distr). call(_:true).

  (* witness are equal *)
  while (={glob A_SH,key,a,b,c,j,ws,js,m1} /\ deg phi{2} <= Bl.t  /\ b{1} <> zero /\
  key{2}.`1 = mkKey Bl.GB.g a{2} /\ phiis{1}.`2 =  phiis{2} /\
  (phiis{1}.`1 :: phiis{1}.`2) = map (peval phi{2}) (js_1{1} :: js{2}) /\ size js{1} = Bl.t -1 /\
  key{2}.`2 = mkKey(Bl.GB.g ^ asint b{2}) a{2}  /\ 
  d{1} = m1{1} /\ d{2} = inv b{2} ** (m1{2} - phi{2}) /\ deg m1{1} <= Bl.t  /\ 0 <= j{1}).

  auto. progress.

  (* - witness exp is equal *) 
  rewrite -peval_mul -peval_add. rewrite H3. rewrite (nth_map zero). smt(). rewrite -peval_neg. trivial.

  (* - witness group is equal*)
  rewrite !H1 !H5. rewrite !head_mkKey !comPolEval; trivial. smt(degDiv). smt(degDiv).
    apply (lez_trans (deg (inv b{2} ** (m1{2} - phi{2})))). apply degDiv. apply degZ_le_gen. apply degD_sim; trivial.
  rewrite degN; trivial. 
  rewrite -!Bl.GB.expM. rewrite -!Bl.GB.expD. apply Bl.exp_GB_can2. apply Bl.GP.pow_bij.
  rewrite !inzmodD !inzmodM !asintK. rewrite ediv_scale_1. apply Xi_neq_0. rewrite ediv_add_1.
    apply Xi_neq_0. rewrite ediv_neg_1. apply Xi_neq_0. rewrite -peval_mul. 
  have : b{2} * (peval ((edivpoly m1{2} (X - polyC (nth zero js{2} j{2}))).`1 -
    (edivpoly phi{2} (X - polyC (nth zero js{2} j{2}))).`1) a{2} * inv b{2}) =
      peval ((edivpoly m1{2} (X - polyC (nth zero js{2} j{2}))).`1 -
    (edivpoly phi{2} (X - polyC (nth zero js{2} j{2}))).`1) a{2}.
  rewrite -(Bl.GP.ZModE.ZModpField.mulrC (inv b{2})). rewrite Bl.GP.ZModE.ZModpField.mulrA. rewrite Bl.GP.ZModE.ZModpField.mulrV.
      trivial.  smt(@Bl.GP.ZModE.ZModpField). move => g. rewrite g. rewrite -peval_add -peval_neg. smt(@Bl.GP.ZModE.ZModpField).
  smt().

  (* closing *)
  auto. progress. have : interpolate (js_1{1} :: js{2}) (phiis{1}.`1 :: phiis{1}.`2) = phi{2}. apply interpolate_corr; trivial.
      smt(@List). smt(@List). move => h. rewrite -h.  smt().

   auto. call{1} (: true ==> true).  call{2} (: true ==> true).
  while(={j,js} /\ ! uniq js{1}). auto. progress.  auto. rnd{1}. rnd{2}.
  rnd{1}. auto. progress. apply dcond_ll. apply mu_FD; trivial. apply dpoly_ll. smt(@Bl.FD). smt(). trivial. trivial.   
qed.

lemma PolyComPed_Strong_Hiding  &m :
    islossless A_SH.setup =>
    islossless A_SH.choose =>
    islossless A_SH.guess =>
    Pr[Strong_Hiding(PolyCommitPed,PolyCommitPed_A,A_SH).real() @ &m : res] <= (1%r/ Bl.GB.order%r).
proof.
   move => As_ll Ac_ll Ag_ll. 
   have : forall (b a c : real), a <= b => b <= c => a <= c. smt(). move=> h'.
  apply (h' Pr[HidingSimpS(A_SH).comm_sim() @ &m : res]). apply SHiding_equiv1; trivial.
  rewrite -(SHiding_equiv2); trivial. apply (h' Pr[HidingSimpS(A_SH).rand() @ &m : res]).
  apply (HidingSimp_FlipS &m); trivial. rewrite (Hiding_BoundS &m);trivial. 
qed.

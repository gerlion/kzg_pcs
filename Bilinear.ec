(* This is a modified version of https://github.com/ZooCrypt/AutoGnP/blob/master/ZooLib/Bilinear.ec *)
require import AllCore StdRing StdOrder Distr List FSet Group IntDiv Dexcepted DList.
(*---*) import RField RealOrder.

theory Bl.

(* Spin in the the groups *)

clone CyclicGroup as GB. (* Base Group *)
axiom prime_p : IntDiv.prime GB.order.

clone CyclicGroup as GT.
axiom prime_q : IntDiv.prime GT.order.

(* We are consider two froups of the prime order,
  since order/card is a defined operator not an axiom we
  cannot say they are equal in a better way than this  *)
axiom order_eq : GB.order = GT.order.

clone GT.PowZMod as GP with
  lemma prime_order <- prime_q.
    
  
clone GB.PowZMod as GPB with
  lemma prime_order <- prime_p.

clone GP.FDistr as FD.

op e : GB.group -> GB.group -> GT.group.

axiom e_g_g : e GB.g GB.g = GT.g.

axiom eND : e GB.g GB.g <> GT.e.

import GB GT GP FD.

axiom e_pow1 (g f:GB.group) (x:int) : e (g^x) f = (e g f)^x.
axiom e_pow2 (g f:GB.group) (x:int) : e g (f^x) = (e g f)^x.

op t : int.
axiom t_valid : 1 <= t.
axiom t_lt_card : t < GT.order.

  (* Helpful lemmas on sampling *)

lemma FD_nin a :  mu Bl.FD.dt (fun (b : exp) => b <> a) = 1%r - (1%r / Bl.GB.order%r).
proof.
  rewrite mu_not. have : weight Bl.FD.dt= 1%r. smt(@Bl.FD). move => h. rewrite h. congr. congr. rewrite Bl.FD.dt1E. smt(order_eq).
qed.

lemma dlist_nin a t : 0 <= t =>  mu (dlist Bl.FD.dt t) (fun (x : exp list) => ! a \in x) = (1%r - (1%r / Bl.GB.order%r)) ^ t.
proof.
  move => ge0_t. pose p (b : exp) := b <> a .    
  pose I := FSet.oflist (range 0 t).    
  pose P (xs : exp list) := forall (i : int), FSet.mem I i => p(nth Bl.GP.ZModE.zero xs i).
  rewrite (mu_eq_support _ _ P). move => x x_dl. simplify. rewrite /P /I /p. rewrite (nthPn ZModE.zero). smt(@List @FSet @DList).
  rewrite /P. rewrite (dlist_setE Bl.GP.ZModE.zero Bl.FD.dt p t I). smt(@GP). smt().
  rewrite /I. move => i. rewrite FSet.mem_oflist. smt(@List). have : FSet.card I = t. rewrite /I. smt(@List @FSet).
  move => h. rewrite h. rewrite FD_nin. trivial.
qed.

lemma dlist_in a t : 0 <= t =>  mu (dlist Bl.FD.dt t) (fun (x : exp list) => a \in x) = 1%r - ((1%r - (1%r / Bl.GB.order%r)) ^ t).
proof.
  move => ht. have : predC (predC (fun (x : exp list) => a \in x)) = (fun (x : exp list) => a \in x). 
  smt(). move => h. rewrite -h. rewrite mu_not. rewrite dlist_nin. trivial. smt(t_valid @DList @GP).
qed.


(* Helpful leamms for ZMod *)
lemma eq_inzmod i j : 0 <= i < GT.order => 0 <= j < GT.order =>
    Bl.GP.ZModE.inzmod i = Bl.GP.ZModE.inzmod j <=> i = j.
proof.
  move => h0 h1. split => h2. rewrite -Bl.GP.ZModE.asint_eq in h2.
  rewrite !Bl.GP.ZModE.inzmodK in h2. smt(@IntDiv prime_q). rewrite h2. trivial.
qed.

lemma exp_g_modz (g : Bl.GB.group) k : g ^ (k %% GB.order) = g ^ k.
proof.
  elim (GB.log_spec g) => k' hk'. elim hk' => h h'. rewrite -h'. smt(@GB).
qed.

lemma g_neq_e :
    Bl.GB.g <> Bl.GB.e.
proof.
  case (Bl.GB.g = Bl.GB.e) => h; trivial. rewrite -(GB.exp1 GB.g) in h. rewrite -(GB.exp0 GB.g) in h. smt(@GB @GPB.ZModE).
qed.

(* For easy movement between cyclic and non-cyclic group exp *)
lemma exp_gt_eq b (e:exp) : GT.( ^ ) b (ZModE.asint e) = GP.( ^ )b e.
    smt(). qed.

lemma exp_modz_gt (b : group) : b ^ GT.order = GT.e.
  rewrite -expgK. rewrite -exp_gt_eq. move => @/ loge. rewrite logMr. rewrite ZModE.inzmodK.
  have : GT.order * log b %% GT.order %% GT.order = 0. smt(@IntDiv). move => h. rewrite h.
  apply GT.exp0.
qed.
  
lemma exp_gt_eq2 b (e:int) : GT.( ^ ) b e = GP.( ^ )b (ZModE.inzmod e).
    rewrite -exp_gt_eq. rewrite ZModE.inzmodK. rewrite {1}(divz_eq e GT.order).
    rewrite mulrC. rewrite expD. rewrite expM. rewrite exp_modz_gt. by rewrite expc1 mul1c.
  qed.

lemma exp_gb_eq b (e:GPB.exp) : GB.( ^ ) b (GPB.ZModE.asint e) = GPB.( ^ )b e.
    smt(). qed.


lemma exp_modz_gb (b : GB.group) : b ^ GB.order = GB.e.
    rewrite -expgK. rewrite logMr. have : GB.order * log b %% GB.order = 0. smt(@IntDiv). move => h.
    rewrite h. apply GB.exp0.
qed.  

lemma exp_gb_eq2 b (e:int) : GB.( ^ ) b e = GPB.( ^ )b (GPB.ZModE.inzmod e).
    move => @/inzmod. rewrite -exp_gb_eq. 
    have : b ^ (GPB.ZModE.asint ((GPB.ZModE.Sub.insubd (e %% GB.order)))) = b ^ (e %% GB.order). smt(GPB.ZModE.inzmodK).
    move => h'. rewrite h'. rewrite {1}(divz_eq e GB.order).
    rewrite mulrC. rewrite expD. rewrite expM. rewrite exp_modz_gb. by rewrite expc1 mul1c.
qed.

lemma loge_log x y : ZModE.inzmod (GB.log x) = ZModE.inzmod (GB.log y)  <=> GPB.loge x = GPB.loge y.
proof.
  move => @/loge. split; move => h0. apply GPB.ZModE.asint_eq. rewrite -ZModE.asint_eq in h0.

  rewrite !GPB.ZModE.inzmodK. rewrite !ZModE.inzmodK in h0. rewrite !order_eq. trivial.
  rewrite -GPB.ZModE.asint_eq in h0. apply ZModE.asint_eq. 
  rewrite !GPB.ZModE.inzmodK in h0. rewrite !ZModE.inzmodK. rewrite !order_eq in h0. trivial.
qed.

import GP.ZModE.

lemma log_neq_zero z : z <> GB.e => inzmod (log z) <> zero.
proof.
  move => h. case (inzmod (log z) = zero); trivial. move => h'. have : log z = 0. smt(@GB @ZModE order_eq).
  smt(@GB).
qed.

(*************************************)
(* lemmas for moving around elements *)
(*************************************)

lemma GPB_pow_bij g (x y : GPB.exp) : g <> GB.e => x = y <=> GPB.( ^ ) g x = GPB.( ^ ) g y.
    smt(@GPB).
qed.
  
lemma GT_move_right (a b c : GT.group) :
      a * b = c <=> a = c / b.
proof.
  split; move => h. smt(@GT). smt(@GT).
qed.

lemma GT_shuffle (a b c d : Bl.GT.group) :
    a * b = c * d <=>  a / d = c / b.
proof.
  split; move => g1. rewrite GT_move_right in g1. rewrite g1. smt(@GP).
  rewrite -GT_move_right in g1. smt(@GT).
qed.

lemma GT_shuffle2 (a b c d : Bl.GT.group) :
    a * b = c * d <=>  a / c = d / b.
proof.
  split; move => g1. rewrite GT_move_right in g1. smt(@GP).
  rewrite -GT_move_right in g1. smt(@GT).
qed.

lemma GB_zero (a b : Bl.GB.group) :
    a = b <=> a / b = Bl.GB.e.
    smt(@Bl.GB).
qed.

lemma GT_zero (a b : Bl.GT.group) :
    a = b <=> a / b = Bl.GT.e.
    smt(@Bl.GP).
  qed.

lemma GB_one : log (GB.g) = 1.
  smt(@GPB @GB prime_p).
qed.
  
lemma GT_one : log (GT.g) = 1.
  smt(@GP @GT prime_q).
qed.


lemma exp_add_right (a b c : exp) : a + b = c <=> a = c - b.
  split; move => h; smt(@ZModE).
qed.


lemma exp_add_left (a b c : exp) : a = c + b <=> a - c = b.
  split; move => h; smt(@ZModE).
qed.

lemma exp_mul_left (a b c : exp) : b <> zero => a * b = c <=> a = c / b.
  move => g. split; move => h; smt(@ZModE).
qed.


lemma exp_div_left (a b c : exp) : c <> zero => b<> zero => a / b = c <=> a / c = b.
  move => h0 h1. split; move => h'; smt(@ZModE).
qed.
  
lemma exp_a_bc (a a' b c c': exp) : c' <> c => a + b *c = a' + b*c' <=> (a-a')/(c'-c) = b.
proof.
  move => g. split => h. rewrite exp_add_right in h. rewrite h. algebra.
  rewrite -h. algebra.
qed.


lemma exp_ab_c (a a' b c c': exp) : c' <> c => a * b + c = a'* b + c' => (a-a')/(c'-c) = one/b.
proof.
  move => g h. rewrite exp_add_right in h. rewrite -ZModpField.addrA in h. rewrite exp_add_left in h.
  rewrite -h. algebra. smt(@ZModpField).  smt(@ZModpField).
qed.

(**************************************************************)
(* Begin lemmas about pairings that follow from bassic axioms *)
(**************************************************************)


lemma e_pow (g f:GB.group) (x y: int) : e (g^x) (f^y) =
    (e g f)^(x * y).
proof.
  rewrite e_pow2 e_pow1. rewrite GT.expM. trivial.
qed.
  
lemma e_inv1 (x y : GB.group): e (inv x) y = inv (e x y).
proof.
  (* rewrite (GPB.inv_def x). rewrite -exp_gb_eq. rewrite e_pow1. *)
  rewrite -(GPB.expgK x). rewrite -exp_gb_eq. rewrite e_pow1.
  rewrite -expN. rewrite exp_gb_eq. rewrite -e_pow1.
  have : forall a b c, a = b => e a c = e b c. smt(). move => h. apply h.
  rewrite expN. rewrite exp_gb_eq. trivial.
qed.
    
lemma e_mul1 x y g2: e x g2 * e y g2 = e (x*y) g2.
proof.
  rewrite -(GB.expgK x) -(GB.expgK y). rewrite -(GB.expD).
  rewrite !e_pow1. rewrite GT.expD. trivial.
qed.

lemma e_div1 x y g2: e x g2 / e y g2 = e (x/y) g2.
proof.
  rewrite -e_mul1. rewrite e_inv1. trivial.    
qed.

lemma e_mul1_big x g2 :
  e (List.foldr Bl.GB.( * ) Bl.GB.e x) g2 =
    List.foldr Bl.GT.( * ) (e GB.e g2) (map (fun xi => e xi g2) x).
  proof.
    elim x. simplify. trivial. move => x l h. simplify. rewrite- e_mul1. rewrite h. trivial.
  qed.

lemma e_mul2 g1 x y: e g1 x * e g1 y = e g1 (x*y).
proof.
  rewrite -(GB.expgK x) -(GB.expgK y). rewrite -(GB.expD).
  rewrite !e_pow2. rewrite GT.expD. trivial.
qed.

lemma e_mul2_big g1 x :
  e g1 (List.foldr Bl.GB.( * ) Bl.GB.e x) =
    List.foldr Bl.GT.( * ) (e g1 Bl.GB.e) (map (fun xi => e g1 xi) x).
  proof.
    elim x. simplify. trivial. move => x l h. simplify. rewrite- e_mul2. rewrite h. trivial.
qed.

lemma e_mul_gen (x x' : GB.group) (y y' z z' : int) :
    e x (Bl.GB.g^y) * e (Bl.GB.g^y') Bl.GB.g =
    e x' (Bl.GB.g^z) * e (Bl.GB.g^z') Bl.GB.g =>
    inzmod (log x) * (inzmod y) + (inzmod y') = inzmod (log x') * (inzmod z) + (inzmod z').
proof.
  rewrite -(GB.expgK x) -(GB.expgK x'). rewrite !e_pow !e_pow1 !e_g_g. rewrite -!GT.expD. move => h.
  rewrite !exp_gt_eq2 in h. rewrite -GP.pow_bij in h. rewrite !GB.logK. rewrite order_eq.
  rewrite !inzmodD in h. rewrite !inzmodM in h. rewrite -!inzmod_mod. trivial.
qed.

lemma log_e (x:GB.group) (y:GB.group):
  log (e x y) = log x * log y %% GT.order.
proof.
  rewrite -{1}(GB.expgK x) -{1}(GB.expgK y) e_pow. rewrite e_g_g.
  rewrite GT.logK. trivial.
qed.

lemma log_e_g x : loge (e GB.g x) = ZModE.inzmod (GB.log x).
    proof.
      move => @/loge. rewrite log_e. move => @/inzmod. rewrite modz_mod.
      have : log GB.g =1. have : GB.g = GB.g^1. smt(@Bl.GB).
      move => h. rewrite h. rewrite logK. smt(GPB.ZModE.prime_p).
      move => h. rewrite h. smt().
  qed.

lemma log_e_gen x y : loge (e x y) = ZModE.inzmod (GB.log x * GB.log y).
proof.
    move => @/loge. rewrite log_e. move => @/inzmod. rewrite modz_mod. trivial.
qed.

    
lemma GB_e x y : e x GB.g = e y GB.g => x = y.
    move => h0. rewrite -(GB.expgK x) in h0. rewrite -(GB.expgK y) in h0. rewrite e_pow1 in h0.
    rewrite e_pow1 in h0. rewrite e_g_g in h0. rewrite !exp_gt_eq2 in h0. rewrite -pow_bij in h0.
    apply GPB.log_bij. smt(loge_log).
qed.

lemma e_comm x y : e x y = e y x.
proof.
  rewrite -(GB.expgK x) -(GB.expgK y). rewrite !e_pow. smt().
qed.

lemma e_inj1 x y z : z <> GB.e => e x z = e y z => x = y.
    move => h0 h. rewrite -(GB.expgK x) in h. rewrite -(GB.expgK y) in h. rewrite -(GB.expgK z) in h. rewrite !e_pow in h.
    rewrite e_g_g in h. rewrite !exp_gt_eq2 in h. rewrite -pow_bij in h.
    apply GPB.log_bij. have : inzmod (log x) = inzmod (log y). rewrite !inzmodM  in h.
    rewrite exp_mul_left in h. apply log_neq_zero. trivial. smt(@ZModE log_neq_zero). move => h''.  smt(loge_log).
qed.
  
lemma asint_inzmod_asint (a :GPB.exp) :
    GP.ZModE.asint (GP.ZModE.inzmod (GPB.ZModE.asint a)) =
    GPB.ZModE.asint a.
    proof.
      rewrite GP.ZModE.inzmodK. rewrite -order_eq.
      smt(@GPB.ZModE @IntDiv).
  qed.

(***********************************************)
(* various lemmas for handeling multiple group *)
(***********************************************)
    

(* Prove some axiom about asint in the exponent *)   
lemma exp_GB_asint_add (g : GB.group) (x y : exp) : g ^ (ZModE.asint x + ZModE.asint y) = g^(ZModE.asint (ZModE.(+) x y)).
    rewrite -(GPB.expgK g). case (GPB.ZModE.unit (GPB.loge g)); move => h1.
    rewrite GPB.ZModE.unitE in h1. rewrite !exp_gb_eq2. rewrite -!GPB.expM. apply GPB.pow_bij.  smt(@GPB.ZModE order_eq @ZModE).
    rewrite GPB.ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GPB @GB).
qed.
  
lemma exp_GB_asint_mul (g : GB.group) (x y : exp) : g ^ (ZModE.asint x * ZModE.asint y) = g^(ZModE.asint (ZModE.( * ) x y)).
    rewrite -(GPB.expgK g). case (GPB.ZModE.unit (GPB.loge g)); move => h1.
    rewrite GPB.ZModE.unitE in h1. rewrite !exp_gb_eq2. rewrite -!GPB.expM. apply GPB.pow_bij.  smt(@GPB.ZModE order_eq @ZModE).
    rewrite GPB.ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GPB @GB).
qed.

lemma exp_GT_asint_add (g : GT.group) (x y : exp) : g ^ (ZModE.asint x + ZModE.asint y) = g^(ZModE.asint (ZModE.(+) x y)).
    rewrite -(GP.expgK g). case (GP.ZModE.unit (GP.loge g)); move => h1.
    rewrite GP.ZModE.unitE in h1. rewrite !exp_gt_eq2. rewrite -!GP.expM. apply GP.pow_bij.  smt(@ZModE).
    rewrite GP.ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GP @GT).
qed.
  
lemma exp_GT_asint_mul (g : GT.group) (x y : exp) : g ^ (ZModE.asint x * ZModE.asint y) = g^(ZModE.asint (ZModE.( * ) x y)).
    rewrite -(GP.expgK g). case (GP.ZModE.unit (GP.loge g)); move => h1.
    rewrite ZModE.unitE in h1. rewrite !exp_gt_eq2. rewrite -!GP.expM. apply GP.pow_bij.  smt(@ZModE).
    rewrite ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GP @GT).
qed.

lemma exp_GT_asint_add_l (g : GT.group) (x : exp) y : g ^ (ZModE.asint x + y) = g^(ZModE.(+) x (ZModE.inzmod y)).
    rewrite -(GP.expgK g). case (GP.ZModE.unit (GP.loge g)); move => h1.
    rewrite GP.ZModE.unitE in h1. rewrite !exp_gt_eq2. rewrite -!GP.expM. apply GP.pow_bij.  smt(@ZModE).
    rewrite GP.ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GP @GT).
qed.

lemma exp_GT_asint_add_r (g : GT.group) x (y : exp) : g ^ (x + ZModE.asint y) = g^(ZModE.(+)(ZModE.inzmod x) y).
    rewrite -(GP.expgK g). case (GP.ZModE.unit (GP.loge g)); move => h1.
    rewrite GP.ZModE.unitE in h1. rewrite !exp_gt_eq2. rewrite -!GP.expM. apply GP.pow_bij.  smt(@ZModE).
    rewrite GP.ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GP @GT).
qed. 
  
lemma exp_GT_asint_mul_l (g : GT.group) (x  : exp) y : g ^ (ZModE.asint x * y) = g^(ZModE.( * ) x (ZModE.inzmod y)).
    rewrite -(GP.expgK g). case (GP.ZModE.unit (GP.loge g)); move => h1.
    rewrite ZModE.unitE in h1. rewrite !exp_gt_eq2. rewrite -!GP.expM. apply GP.pow_bij.  smt(@ZModE).
    rewrite ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GP @GT).
qed.

lemma exp_GT_asint_mul_r (g : GT.group) x (y : exp) : g ^ (x * ZModE.asint y) = g^(ZModE.( * ) (ZModE.inzmod x) y).
    rewrite -(GP.expgK g). case (GP.ZModE.unit (GP.loge g)); move => h1.
    rewrite ZModE.unitE in h1. rewrite !exp_gt_eq2. rewrite -!GP.expM. apply GP.pow_bij.  smt(@ZModE).
    rewrite ZModE.unitE in h1. apply negbNE in h1. rewrite h1. smt(@GP @GT).
qed.
  

(* Building to a bijection between exp in the two groups *)
lemma GB_g x y : x * GB.g = y * GB.g => x = y.
    smt(@GB).
  qed.


lemma exp_GB (g : GB.group)(g' : GT.group)(x y : exp) : GPB.ZModE.asint (GPB.loge g) = ZModE.asint (GP.loge g')
    => g ^ (ZModE.asint x) = g ^ (ZModE.asint y) <=>
    g' ^ x = g' ^ y.
proof.
  move => @/loge h1. split; move => h0.
  (* part 1 *)
  rewrite -expgK. move => @/loge. rewrite -!exp_gt_eq. rewrite GT.logMr. rewrite eq_sym.
  rewrite -expgK. move => @/loge. rewrite -!exp_gt_eq. rewrite GT.logMr. rewrite GPB.ZModE.inzmodK in h1.
  rewrite ZModE.inzmodK in h1. rewrite -modzMmr. rewrite eq_sym. rewrite -modzMmr. rewrite -!h1.
  rewrite order_eq. rewrite !modzMmr. rewrite -!inzmod_mod. rewrite !inzmodK. rewrite !expg_modz.
  rewrite -e_g_g. rewrite -!e_pow1. congr. rewrite mulrC. smt(@GB).
  (* part 2*)
  apply GB_e. rewrite !e_pow1. rewrite -GPB.expgK. rewrite -!exp_gb_eq. rewrite !e_pow1. rewrite !e_g_g. move => @/loge.
  rewrite h1. rewrite !exp_gt_eq. smt(expgK). 
qed.

lemma exp_GB_can (x y : exp) : GB.g ^ (ZModE.asint x) = GB.g ^ (ZModE.asint y) <=>  GT.g ^ x = GT.g ^ y.
  apply exp_GB. smt(@GPB @GP).
qed.

lemma exp_GB_can2 (x y : int) : GB.g ^ x = GB.g ^ y <=>
    GT.g ^ (ZModE.inzmod x) = GT.g ^ (ZModE.inzmod y).
    split; move => h.
    rewrite -exp_GB_can. rewrite !ZModE.inzmodK. rewrite -!order_eq. rewrite !GB.expg_modz.
    trivial. rewrite -exp_GB_can in h. rewrite !ZModE.inzmodK in h. rewrite -!order_eq in h.
    rewrite !GB.expg_modz in h. trivial.
  qed.

lemma exp_GB_can2_gen g (x y : int) : g <> Bl.GB.e => g ^ x = g ^ y <=>
    GT.g ^ (ZModE.inzmod x) = GT.g ^ (ZModE.inzmod y).
    move => h'. split; move => h.
    rewrite -exp_GB_can. rewrite !exp_gb_eq2. rewrite !exp_gb_eq2 in h. rewrite -GPB_pow_bij in h. trivial.
    smt(order_eq @GPB).
    (* Case 2 *)
    rewrite -pow_bij in h. have : asint (inzmod x) = asint (inzmod y). smt(). move => h''.
    rewrite !inzmodK in h''. rewrite -Bl.order_eq in h''. rewrite -(GB.expgK g). smt(@Bl.GB).
  qed.

lemma exp0_cus a : GB.( ^ )a (asint zero)%Bl.GP.ZModE = Bl.GB.e.
        proof. rewrite zeroE. smt(@Bl.GB). qed.

lemma prod_sum_eq g a m:
      foldr Bl.GB.( * ) Bl.GB.e
      (mkseq (fun (i : int) => GB.( ^ ) g (asint (nth a m i))) (size m)) =
      g ^ asint (foldr Bl.GP.ZModE.( + ) Bl.GP.ZModE.zero m).
  proof. 
    elim m. simplify. rewrite mkseq0. simplify. rewrite exp0_cus.
    trivial.
    (* inductive case *)
    move => x l h. simplify. have : g ^ (asint (Bl.GP.ZModE.( + ) x
      (foldr Bl.GP.ZModE.(+) Bl.GP.ZModE.zero l)))
  = Bl.GB.( * ) (g ^ (asint x))
  (g ^ (asint (foldr Bl.GP.ZModE.(+) Bl.GP.ZModE.zero l))). 
  rewrite -Bl.GB.expD. rewrite eq_sym. apply (Bl.exp_GB_asint_add).
    move => h'. rewrite h'. rewrite -h. rewrite mkseq_add. smt(). smt(@List). rewrite List.foldr_cat.
    rewrite mkseq1. simplify. simplify. have : forall a b c,
    b = c => Bl.GB.( * ) a b = Bl.GB.( * ) a c. move => a0 b c h''. smt(). move => h''. apply h''.
    apply eq_foldr; trivial. apply (eq_from_nth Bl.GB.g). smt(@List).
  move => i g'.
    rewrite size_mkseq in g'. rewrite nth_mkseq. smt(). rewrite nth_mkseq. smt(). simplify.
    smt().
qed.

hint rewrite Ring.rw_algebra : e_g_g log_e.


(* Security properties, DLOG in both groups and t-SDH *)
module type DLogAdv = {
  proc guess(g : GB.group) : exp
}.

module DLogExp (A:DLogAdv) = {
    proc main () : bool = {
      var x, x';
      x  <$ dt;
      x' <@ A.guess(GB.g ^ (ZModE.asint x));

      return (x' = x);
    }
  }.

  module type TsdhAdv = {
    proc comp(ga : GB.group list) : exp * GB.group
  }.

import ZModE.

op mkKey = fun (a : exp) =>  mkseq (fun (i:int) =>  Bl.GB.g^(asint (exp a i))) (Bl.t+1).
lemma mkKeyBij a b : mkKey a = mkKey b <=> a = b. 
proof.
  split => h. apply pow_bij.  have : nth GB.g (mkKey a) 1 = nth GB.g (mkKey b) 1.  smt(t_valid @List).
  rewrite !nth_mkseq. smt(t_valid). smt(t_valid). simplify. move => h'. apply exp_GB_can. smt(@ZModE). smt().
qed.

module Tsdh(A:TsdhAdv) = {
  proc main () : bool = {
    var a, b, c, d;
    a <$ dt;
    b <- mkKey a;
    (c,d) <@ A.comp(b);
    return (c <> - a /\ d = GB.g^(asint(ZModE.one / (a+ c))));
  }
}.


module type TsdhAdv2 = {
    proc comp(ga : (GB.group * GB.group) list) : (exp -> exp) * (exp -> GB.group) 
  }.

(* This is a variant of Tsdh for use in PolyBind and EvalBind of PolyComPed *)
(* It loses one bit of security of the normal version *)
module Tsdh2(A:TsdhAdv2) = {
  var winl, winr : bool
  
  proc main () : bool = {
    var a, a', b, b', c, d;
    a <$ dt;
    a' <$ dt;
    b <- map (fun (i:int) =>GB.g^(ZModE.asint (exp a i))) (range 0 (t+1));
    b' <- map (fun (i:int) =>(GB.g^(asint a'))^(ZModE.asint (exp a i))) (range 0 (t+1)); 
    (c,d) <@ A.comp(zip b b');
    winl <- c a = a'; (* either find a', the discrete log or solve tsdh*)
    winr <- c a' <> - a /\ d a' = GB.g^(asint(ZModE.one / (a+ c a')));
    return winl \/ winr;
  }
}.

module TsdhAdv2_dlog (A : TsdhAdv2) = {
  proc guess(g : GB.group) : exp = {
    var a, b, b', c,d;
    a <$ dt;
    b <- map (fun (i:int) =>GB.g^(ZModE.asint (exp a i))) (range 0 (t+1));
    b' <- map (fun (i:int) =>g^(ZModE.asint (exp a i))) (range 0 (t+1)); 
    (c,d) <@ A.comp(zip b b');
    return c a;
  }
}.
  
module TsdhAdv2_Tsdh (A : TsdhAdv2) = {
  proc comp(ga : GB.group list) : exp * GB.group = {
    var a, b', c, d;
    a <$ dt;
    b' <- map (fun (x : GB.group) => x^(ZModE.asint a)) ga;
    (c,d) <@ A.comp(zip ga b');
    return (c a, d a);
  }
}.

lemma Tsdh2_Hard_sub  (A <: TsdhAdv2) &m :
  Pr[Tsdh2(A).main() @ &m : res] <= Pr[Tsdh2(A).main() @ &m : Tsdh2.winl] + Pr[Tsdh2(A).main() @ &m : Tsdh2.winr].
proof.
  byequiv. proc. inline *. wp. call(_:true). auto. progress. smt(). smt().
qed.

lemma Tsdh2_Hard_left (A <: TsdhAdv2) &m :
  Pr[Tsdh2(A).main() @ &m : Tsdh2.winl] = Pr[DLogExp(TsdhAdv2_dlog(A)).main() @ &m : res].   
proof.
  byequiv. proc. inline *. wp. call( : true). swap{2} [1..2] 1. auto. progress. smt().
qed.

lemma Tsdh2_Hard_right (A <: TsdhAdv2) &m :
  Pr[Tsdh2(A).main() @ &m : Tsdh2.winr] = Pr[Tsdh(TsdhAdv2_Tsdh(A)).main() @ &m : res].
proof.
  byequiv. proc. inline *. wp. call(:true). swap{2} 4 -2. auto. progress. congr. move => @/mkKey.
  apply (eq_from_nth GB.g). smt(@List). move => i hi. rewrite (nth_map 0). smt(@List).
  rewrite (nth_mkseq GB.g). smt(@List).  rewrite nth_range. smt(@List). simplify. trivial.
  apply (eq_from_nth GB.g). smt(@List). move => i hi. rewrite (nth_map 0). smt(@List).
  rewrite (nth_map GB.g). smt(@List). rewrite (nth_mkseq GB.g). smt(@List). rewrite nth_range. smt(@List).
  simplify. smt(@GB). smt(). smt(). 
qed.
  
lemma Tsdh2_Hard (A <: TsdhAdv2) &m :
    Pr[Tsdh2(A).main() @ &m : res] <=
    Pr[DLogExp(TsdhAdv2_dlog(A)).main() @ &m : res] + Pr[Tsdh(TsdhAdv2_Tsdh(A)).main() @ &m : res].
proof.
  rewrite -(Tsdh2_Hard_left A &m). rewrite -(Tsdh2_Hard_right A &m). apply (Tsdh2_Hard_sub A &m).
qed.

(* Variant of DLog where adversarts wins if either of two challenges is solve*)
module type DLog2Adv = {
  proc guess(g : GB.group*GB.group) : exp -> exp
}.

module DLog2Exp (A:DLog2Adv) = {
  var winl, winr : bool
  
    proc main () : bool = {
      var a, b, c;
      a  <$ dt;
      b  <$ dt;
      c <@ A.guess(GB.g ^ (ZModE.asint a), GB.g ^ (ZModE.asint b));

      winl <- c b = a; 
      winr <- c a = b;
    
     return winl \/ winr;
    }
  }.

module DLog2Adv_dlog1 (A : DLog2Adv) = {
  proc guess(g : GB.group) : exp = {
    var b, c;
    b <$ dt;
    c <@ A.guess(g,GB.g ^ (ZModE.asint b));
    return c b;
  }
}.
  
module DLog2Adv_dlog2 (A :  DLog2Adv) = {
  proc guess(g : GB.group) : exp= {
    var a,  c;
    a <$ dt;
    c <@ A.guess(GB.g ^ (ZModE.asint a),g);
    return c a;
  }
}.

section DLog2Check.

declare module A_dl2 <: DLog2Adv {-DLog2Exp}.

lemma Dlog2_Hard_sub   &m :
    Pr[DLog2Exp(A_dl2).main() @ &m : res] <=
      Pr[DLog2Exp(A_dl2).main() @ &m : DLog2Exp.winl] + Pr[DLog2Exp(A_dl2).main() @ &m : DLog2Exp.winr].
proof.
  byequiv. proc. inline *. wp. call(_:true). auto. progress. smt(). smt().
qed.

lemma Dlog2_Hard_left &m :
  Pr[DLog2Exp(A_dl2).main() @ &m : DLog2Exp.winl] = Pr[DLogExp(DLog2Adv_dlog1(A_dl2)).main() @ &m : res].   
proof.
  byequiv. proc. inline *. wp. call( : true). swap{2} 2 1. auto. progress. smt().
qed.

lemma Dlog2_Hard_right &m :
  Pr[DLog2Exp(A_dl2).main() @ &m : DLog2Exp.winr] = Pr[DLogExp(DLog2Adv_dlog2(A_dl2)).main() @ &m : res].   
proof.
  byequiv. proc. inline *. wp. call( : true). swap{2} 3 -2. auto. progress. smt().
qed.
  
lemma Dlog2_Hard &m :
    Pr[DLog2Exp(A_dl2).main() @ &m : res] <=
    Pr[DLogExp(DLog2Adv_dlog1(A_dl2)).main() @ &m : res] + Pr[DLogExp(DLog2Adv_dlog2(A_dl2)).main() @ &m : res].
proof.
  rewrite -(Dlog2_Hard_left &m). rewrite -(Dlog2_Hard_right &m). apply (Dlog2_Hard_sub &m).
qed.

end section  DLog2Check.
  

end Bl.



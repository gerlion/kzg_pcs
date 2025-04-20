require import AllCore Distr DList List DProd Real.
require Bigop.

theory AddDistr.

lemma dlistS_join (d : 'a distr) (phiis : 'a*'a list) (t : int) : size phiis.`2 = t - 1 =>
    mu1 (d `*` dlist d (t - 1)) phiis = mu1 (dlist d t) (phiis.`1 :: phiis.`2).
proof.
  move => h. have : t = size (phiis.`1 :: phiis.`2). smt(@List). move => g. rewrite g.
  rewrite dlistS1E; trivial. smt(@Distr).
qed.

lemma dlist_mu1_sub (d : 'a distr)(card : int) : (forall (s : 'a), mu1 d s = 1%r / card%r) =>
    forall t, 0 <= t => forall x, size x = t =>
    mu1 (dlist d t) x = (1%r/card%r)^(t).
proof.
  move => h.
  apply intind. smt(@List @Real @Distr @DList).
  (* inductive case*)
  simplify. move => i hi ind_hyp. move => x. elim x. smt(). move => x l g size_x.
  clear g. simplify. have : mu1 (dlist d (i + 1)) (x :: l)  = mu1 (dlist d i) l * mu1 d x.
  smt(@DList @Distr). move => g. rewrite g. rewrite ind_hyp. smt(@List). rewrite h. smt(@Real).
qed.

lemma dlist_mu1 (d : 'a distr)(t card : int)(x : 'a list) : size x = t =>
    (forall (s : 'a), mu1 d s = 1%r / card%r) =>
    mu1 (dlist d t) x = (1%r/card%r)^(t).
proof.
  move => g g'. apply dlist_mu1_sub; trivial. smt(@List).
qed.

lemma mu_list (d : 'a distr)(l : 'a list) card : (card - size l)%r / card%r <= mu d (fun x => ! (x \in l))  =>
    size l < card => 0%r < mu d (fun x => ! (x \in l)).
proof.
  move => h h'. elim h => h. have : forall (a b c: real), a < b => b < c  => a < c. smt(). move => g.
  apply (g _ ((card - size l)%r / card%r)). smt(@Real @Int @List). trivial. rewrite -h.  smt(@Real @Int @List).
qed.

lemma mu_not_x (d : 'a distr) a : (exists a', a' \in d /\ a' <> a) => 
  0%r < mu d (predC (pred1 a)).
proof.
  smt(@Distr).
qed.

lemma in_not_x (d : 'a distr) a j n : 0 <= n =>
    j \in dlist (dcond d (predC (pred1 a))) n =>
    !(a \in j).  
proof.
  move => h h'. apply negP => g. rewrite supp_dlist in h'; trivial.
  have : (support (dcond d (predC (pred1 a)))) a. smt(@List). smt(@Distr). 
qed.

lemma dlet_dmap (d : 'a distr) a n : a \in dlet d (fun x => dmap (dlist d n) (fun y => (x,y))) =>
    a.`2 \in dlist d n.
proof.
  move => h. rewrite supp_dlet in h. elim h => a' h.  smt(@Distr).
qed.

axiom dlet_dmap_mu1 (d : 'a distr) n x : 0 <= n =>
    mu1 (dlet d (fun phid0 =>dmap (dlist d n) (fun phiis => (phid0, phiis)))) x =
    mu1 (dlist d (n + 1)) (x.`1::x.`2).

lemma dlist_in_full (d : 'a distr) l t : is_full d => size l = t =>
    l \in dlist d t.
proof.
  smt(@Distr @DList).
qed.

lemma dlist_in_funiform (d : 'a distr) n n' x x' : is_funiform d =>  n = n' =>
     size x =n => size x' = n' =>
    mu1 (dlist d n) x = mu1 (dlist d n') x'.
proof.
move => d_funi nn' size_x size_x'. rewrite !dlist1E. smt(@List). smt(@List).
  rewrite size_x. rewrite size_x'. simplify. rewrite (StdBigop.Bigreal.BRM.big_nth witness).
  rewrite eq_sym. rewrite (StdBigop.Bigreal.BRM.big_nth witness).
  rewrite size_x'. rewrite size_x. rewrite nn'. apply StdBigop.Bigreal.BRM.eq_big. smt().
  smt(). 
qed.

end AddDistr.
             

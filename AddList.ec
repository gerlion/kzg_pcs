require import AllCore List.

(* If a list is equal to the identity at all points
      then the product of the list is the identity *)
  lemma foldr_id (a : 'a list) (ope : 'a->'a->'a) (id : 'a) :
     ope id id = id =>
     all (fun b => b = id) a => foldr ope id a = id.
  proof.
    move => eq. elim a. smt(). move => a' a h h'. simplify. rewrite h. smt(). have : a' = id. smt().
    move => h''. rewrite h''. apply eq.
  qed.

  lemma foldr_id_nth_sub (a : 'a list) (ope : 'a->'a->'a) (id : 'a) :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) => 
     forall i, 0 <= i =>  all (fun b => b = id) (rem (nth id a i) a) => foldr ope id a = nth id a i.
  proof.
  move => eq com. elim a. smt(). move => a' a h i hi h'. simplify. case(i = 0) => h''. rewrite foldr_id. trivial. smt().
    smt(). smt(). rewrite (h (i -1)). smt(). smt(@List). have : a' = id.  smt(@List). move => h'''. rewrite h'''. smt().
qed.

  lemma foldr_id_nth (a : 'a list) (ope : 'a->'a->'a) (id : 'a) i :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) => 
     all (fun b => b = id) (rem (nth id a i) a) => foldr ope id a = nth id a i.
  proof.
    case (i < 0). move => hi eq com all. rewrite nth_neg; trivial. rewrite foldr_id; trivial.
    smt(). smt(@List). smt(foldr_id_nth_sub).
qed.

  lemma foldr_ann_in (a : 'a list) (ope : 'a->'a->'a) (id b : 'a) :
     (forall a, ope a id = id) =>
     (forall a b, ope a b = ope b a) =>
     id \in a => foldr ope b a = id.
  proof.
  move => ann com. elim a. smt(@List). move => x l ind_hyp h. simplify. case (x = id) => g.
  rewrite g. rewrite com. apply ann. rewrite ind_hyp. smt(). apply ann.
qed.

  lemma mkseq_index (f : int -> 'a) (i j : int) : 0 <= i < j => index (f i) (mkseq f j) <= i.
  proof.  
    move => h. have : f i = nth witness (mkseq f j) i. rewrite nth_mkseq. smt(). trivial. move => h'. rewrite h'. smt(@List).
  qed.
  
  (* If predicate holds for every element in a list then it is true for the element at every index *)
  lemma all_nth p x0 (l : 'a list): 
    all p l <=> (forall i, 0 <= i < size l => p (nth x0 l i)).
      proof. elim l. smt(). move => x l h. split. 
        move => h'. elim h'. move => h' h'' i. case (i = 0). move => h'''. smt().
          move => h'''. move => h''''. rewrite (h) in h''. rewrite h'''. simplify.
          apply h''. smt().
        move => h'. simplify. split. apply (h' 0). smt(@List). apply h. move => i h''.
        have : p (nth x0 (x :: l) (i+1)). apply h'. smt(). smt().
    qed.
    
  lemma foldr_cat (mul : 't -> 't-> 't) e a b :
    (forall b, mul e b = b) =>
    (forall a b c, mul (mul a b) c = mul a (mul b c)) =>  
    foldr mul e (a ++ b) = mul (foldr mul e a)
    (foldr mul e b).
  proof.
    elim a. simplify. smt(). move => x h l id ass. simplify. rewrite l. smt().  smt(). rewrite ass. trivial.
  qed.

  lemma eq_foldr_trunc zero (add : 't -> 't -> 't) m m' :
    (forall (b : 't), add zero b = b) =>
    (forall a b c, add (add a b) c = add a (add b c)) =>
    (forall a b, add a b = add b a) =>
    (forall i, 0<= i < max (size m)(size m') => nth zero m i = nth zero m' i) =>
    foldr add zero m =  foldr add zero m'.
  proof.
    move => id ass comm h. case (size m <= size m'); move => h'. rewrite -(cat_take_drop (size m) m'). rewrite foldr_cat; trivial.
    rewrite (foldr_id (drop (size m) m')). smt(). apply (all_nth _ zero). move => i g. simplify.
    rewrite nth_drop. smt(@List). smt(@List). rewrite -h. smt(@List). smt(@List). rewrite comm. rewrite id.
    apply eq_foldr; trivial. apply (eq_from_nth zero). smt(@List). move => i g. smt(@List).
    (* case 2 *)
    rewrite -(cat_take_drop (size m') m). rewrite foldr_cat; trivial. rewrite (foldr_id (drop (size m') m)). smt().
    apply (all_nth _ zero). move => i g. simplify. rewrite nth_drop. smt(@List). smt(@List). rewrite h. smt(@List).
    smt(@List). rewrite comm. rewrite id. apply eq_foldr; trivial. apply (eq_from_nth zero). smt(@List). move => i g. smt(@List).
  qed.    

  lemma foldr_const (add : 't -> 't -> 't) (a : 't list) :
      (forall a b, add a b = add b a) =>
      (forall a b c, add (add a b) c = add a (add b c)) =>
      forall (x b : 't), foldr add (add b x) a = add x (foldr add b a).
  proof.
    elim a. move => comm ass x b. simplify. smt(). move => x a ind_hyp comm ass x0 b0. simplify. rewrite ind_hyp; smt().
  qed.
      
  lemma foldr_foldl_eq (add : 't -> 't -> 't)(a : 't list) :
     (forall a b, add a b = add b a) =>
     (forall a b c, add (add a b) c = add a (add b c)) =>
     forall b, foldr add b a =  foldl add b a.
  proof.
    elim a. simplify. trivial. move => x l ind_hyp comm ass. move => b. simplify. rewrite -ind_hyp; trivial.
    rewrite foldr_const; trivial.
  qed.
      
  lemma foldr_add_distr_sub (add : 't -> 't -> 't)(zero : 't)(a: 't list) :
      (forall h, add zero h = h) =>
      (forall a b, add a b = add b a) =>
      (forall a b c, add (add a b) c = add a (add b c)) =>
    forall b, size a <= size b =>
    add (foldr add zero a) (foldr add zero b) =
    foldr add zero (mkseq (fun (i : int) => add (nth zero a i) (nth zero b i)) (max (size a) (size b))).  
   proof.
    (* base case *)   
   elim a. move => id com ass h b. simplify.   (* inductive case *)
   rewrite id. apply eq_foldr; trivial.
    apply (eq_from_nth zero). smt(@List). move => i h''. rewrite nth_mkseq. smt(). simplify. smt().
   (* inductive case *)
   move => x a ind_hyp id comm ass b. elim b. smt(@List). move => x0 b ind_hyp2 h. simplify.
   have : forall (a b c d : 't), add (add a b) (add c d) = add (add a c) (add b d). smt().
   move => g. rewrite g. rewrite ind_hyp; trivial. smt(). 
   (* simplify orders *)
   have :  max (size a) (size b) = size b. smt(@Int @List).
   move => h'. rewrite h'. have : max (1 + size a)(1+ size b) = size b + 1. smt(@Int @List). move => h''. rewrite h''.
   (* *)
     rewrite mkseqSr. smt(@List). simplify. have : forall a b b' n, (forall i, 0 <= i => b i = b' i) =>
     add a (foldr add zero (mkseq b n)) = add a (foldr add zero (mkseq b' n)). smt(@List). move => g'. apply g'.
     move => i g''. move => @/(\o). simplify. smt(@Int).
  qed.

  lemma foldr_eq_partL (mul : 't -> 't -> 't) e a b  :
   (forall (b0 : 't), mul e b0 = b0) =>
   (forall a b, mul a b = mul b a) =>   
   (forall (a0 b0 c : 't), mul (mul a0 b0) c = mul a0 (mul b0 c)) =>
    size a <= size b =>
    a = take (size a) b =>
    all (fun a => a = e) (drop (size a) b) =>
    foldr mul e a = foldr mul e b.
  proof.
    move => id comm ass h h' h''. rewrite -(cat_take_drop (size a) b). rewrite foldr_cat; trivial. rewrite -h'.
    rewrite (foldr_id (drop (size a) b)). smt(). trivial. smt().
  qed.

  lemma foldr_eq_partR (mul : 't -> 't -> 't) e a b  :
   (forall (a b : 't), a = b <=> b = a) =>
   (forall (b0 : 't), mul e b0 = b0) =>
   (forall a b, mul a b = mul b a) =>   
   (forall (a0 b0 c : 't), mul (mul a0 b0) c = mul a0 (mul b0 c)) =>
   size b <= size a =>
    b = take (size b) a =>
    all (fun a => a = e) (drop (size b) a) =>
    foldr mul e a = foldr mul e b.
  proof.
    move => eq id comm ass h h' h''. rewrite eq. apply foldr_eq_partL; trivial.
  qed.
  
  lemma mkseq_nth_mkseq (a : 'a)(c : 'c)(f : int -> 'a)(f' : int -> 'b)
      (g : 'a -> 'b -> 'c)(s s' : int) :
      0 <= s => s <= s' =>
      mkseq (fun (i : int) => g (nth a (mkseq f s') i) (f' i)) s =
      mkseq (fun (i : int) => g (f i) (f' i)) s.
  proof.
    move => h h'. apply (eq_from_nth c). smt(@List). move => i h'''. rewrite nth_mkseq. smt(@List).
    rewrite nth_mkseq. smt(@List). simplify. rewrite nth_mkseq. rewrite size_mkseq in h'''.
    split. smt(@List). move => h''''. smt(). trivial.
  qed.

  lemma dis_neg (add : 't -> 't -> 't) (neg : 't -> 't) zero m:
    (neg zero = zero) =>
    (forall x y, neg (add x y) = add (neg x) (neg y)) =>
    neg (foldr add zero m) =
    foldr add zero ((map neg) m).
  proof.
    elim m. simplify. trivial.
    (* induction *)
    move => x l ind_hyp neg_zero dist. simplify. rewrite -ind_hyp; trivial. smt().
  qed.

  lemma dis_mul_add (add : 't -> 't -> 't)(mul : 't -> 't -> 't) zero m e:
      (forall b, mul zero b = zero) =>
      (forall a b c, mul (add a b) c = add (mul a c) (mul b c)) =>
      mul (foldr add zero m) e = foldr add zero (map (fun x => mul x e) m).
  proof.
    elim m. move => ann. simplify. smt().
    (* induction *)
    move => x l ind_hyp ann dis. simplify. rewrite -ind_hyp; trivial. smt().
  qed.


lemma rem_nth ['a] (a:'a) (i : 'a) l :
    forall j, 0 <= j => nth a (rem i l) j = nth a l (if j < index i l then j else j + 1).
    elim l. smt().
    move => x l hind j hj. simplify. rewrite index_cons. case (i=x) => h. rewrite h. simplify. have : !(j < 0). smt().
      move => h'. rewrite h'. simplify. have : j +1 <> 0. smt(). move => g. rewrite g. simplify.  trivial.
      have : x<>i. smt(). move => h'. rewrite h'. simplify. case (j < index i l + 1) => g. case (j=0) => g'. trivial.
    rewrite hind. smt(). smt(). have : j <> 0. smt(@List). move => g'. rewrite g'. have : j +1 <> 0. smt(@List).
    move => g''. rewrite g''. simplify. rewrite hind. smt(). smt().
  qed.

  lemma foldr_id_nth_mkseq_sub (ope : 'a->'a->'a) (id : 'a) i j (f : int -> 'a) :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) =>
     (forall (a b c : 'a), ope (ope a b) c = ope a (ope b c)) =>
     0 <= i =>
     0 < j =>
     all (fun b => b = id) (mkseq f i) =>
     all (fun b => b = id) (mkseq (fun x => f (i + (1+ x))) (j-1)) =>
     foldr ope id (mkseq f (i+j)) = f i.
  proof.
    move => eq com ass hi hj h h'. rewrite (mkseq_add _ i j). smt(). smt(). rewrite foldr_cat; trivial. smt().
    rewrite foldr_id; trivial. smt(). rewrite (com id _). rewrite eq. pose q := j -1.  have : j = q + 1. smt(@Int).
    move => g'. rewrite g'. rewrite mkseqSr. smt(). simplify. rewrite foldr_id; trivial. smt(). smt().
  qed.

  lemma foldr_id_nth_mkseq (ope : 'a->'a->'a) (id : 'a) j i (f : int -> 'a) :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) =>
     (forall (a b c : 'a), ope (ope a b) c = ope a (ope b c)) =>
     0 <= i && i < j =>
     all (fun b => b = id) (mkseq f i) =>
     all (fun b => b = id) (mkseq (fun x => f (x + i + 1)) (j-i-1)) =>
     foldr ope id (mkseq f j) = f i.
  proof.
    move => eq com ass hj h h'. pose q := j - i. have : j = i + q. smt(). move => g. rewrite g.
    apply foldr_id_nth_mkseq_sub; trivial. smt(). smt(). smt().
  qed.

  lemma countU (p q : 'a -> bool) (xs : 'a list): count (predU p q) xs = count p xs + count q xs - count (predI p q) xs.
  proof.  
    elim xs. simplify. trivial. move => x l. smt().
  qed.

  lemma countI (p q : 'a -> bool) (xs : 'a list): count (predI p q) xs = count p xs + count q xs - count (predU p q) xs.
  proof.
    rewrite countU. smt().
  qed.

  lemma countC p (s : 'a list):
    count (predC p) s = size s -  count p s.
  proof. elim: s; smt(). qed.

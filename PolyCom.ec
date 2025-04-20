 (* Definition of Polynomial Commitment Scheme - Kate, Zaverucha, Goldberg 2010 *)
require import AllCore Poly List Ring Distr DList.
theory PolynomialCommitment.
  type ck.
  type witness.
  type commitment.
  type openingkey.
  type coeff.

  op t : int.
  axiom t_valid : 1 <= t.
  
  op coeff_sample : coeff distr.
  axiom uni_coeff_sample : is_uniform coeff_sample.
  axiom coeff_sample_ll : is_lossless coeff_sample.

  clone import IDomain as IDCoeff with type t <= coeff.
  
  clone Poly as BasePoly with
    type coeff <- coeff,
    theory IDCoeff <- IDCoeff.
  
  module type PC_Scheme = {
    proc setup() : ck
    proc commit(x: ck, m: BasePoly.poly) : commitment * openingkey
    proc open(x: ck, c: commitment, m: BasePoly.poly, d: openingkey) : BasePoly.poly
    proc verifypoly(x: ck, c: commitment, m: BasePoly.poly, d: openingkey) : bool
    proc createwitness(x: ck, m: BasePoly.poly, i: coeff, d: openingkey) :
      coeff * witness
    proc verifyeval(x: ck, c: commitment, i: coeff, phii: coeff, w: witness) :
      bool
  }.

  type sk.
  
  module type PC_Algorithms = {
    proc valid_key(x : ck) : bool
  }.
  
  module Correctness (S : PC_Scheme) = {
    proc main(p : BasePoly.poly, i : coeff) : bool = {
      var key : ck;
      var c : commitment;
      var d : openingkey;
      var p': BasePoly.poly;
      var b, b' : bool;
      var phii : coeff;
      var w    : witness;
      
      key   <@ S.setup();
      (c,d) <@ S.commit(key, p);
      p'    <@ S.open(key, c, p, d);
      b     <@ S.verifypoly(key, c, p', d);
      (phii, w) <@ S.createwitness(key, p, i, d);
      b'    <@ S.verifyeval(key, c, i, phii, w);

      return (b /\ b') \/ t < BasePoly.deg p;
    }
  }.

  module type AdvPB = { proc forge(key:ck) :
    commitment * BasePoly.poly * BasePoly.poly * openingkey * openingkey }.

  module PolynomialBinding (S : PC_Scheme, A : AdvPB) = {
    proc main() : bool = {
      var key : ck;
      var c : commitment;
      var phi, phi' : BasePoly.poly;
      var d, d' : openingkey;
      var b, b' : bool;
    
      key <@ S.setup();
      (c, phi, phi', d, d') <@ A.forge(key);
      b <@ S.verifypoly(key, c, phi, d);
      b' <@ S.verifypoly(key, c, phi', d');
      
      return (phi <> phi' /\ b /\ b');
     }
  }.

  module type AdvEB = { proc forge(key:ck) : commitment * coeff * 
    coeff * witness *  coeff * witness }.
  
  module EvaluationBinding (S: PC_Scheme, A: AdvEB) = {
    proc main() : bool = {
      var key : ck;
      var c : commitment;
      var i, phii, phii' : coeff;
      var w, w' : witness;
      var b, b' : bool;
      
      key <@ S.setup();
      (c, i, phii, w, phii', w') <@ A.forge(key);
      b  <@ S.verifyeval(key, c, i, phii, w);
      b' <@ S.verifyeval(key, c, i, phii', w');

      return (phii <> phii' /\ b /\ b');
    }
  }.


  (* Hiding *)
  module type AdvH = {
    proc choose(key:ck,c:commitment) : coeff list
    proc guess(phii : coeff list, w: witness list) : coeff * coeff
  }.
  
  module Hiding (S: PC_Scheme, A : AdvH) = {
    
    proc real() : bool = {
      var phi, key; (* The polynomial and commitment scheme key *)
      var c : commitment; (* Commitment to the polynoimal *)
      var i, phii : coeff; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis : coeff list; (* eval at the points in js *)
      var ws : witness list; (* witness to evaluation *)
      var temp1, temp2;
      var j : int;

      phi <$ BasePoly.dpoly t coeff_sample;
      key <@ S.setup();      
      (c, d) <@ S.commit(key, phi);
      
      js <@ A.choose(key,c);
      
      (* construct evaluation points *)
      phiis <- map (fun x => BasePoly.peval phi x) js;
      
      ws <- [];
      j <- 0;
      while (j < t -1) {
        (temp1, temp2) <@ S.createwitness(key, phi, nth IDCoeff.zeror js j, d);
        ws <- temp2 :: ws;
        j <- j +1;
      }  
      
      (i, phii) <@ A.guess(phiis,ws);

      return (phii = BasePoly.peval phi i /\ ! i \in js /\ size js = t-1 /\ uniq js);
    }
  }.

  (* Strong Hiding *)
  module type AdvSH = {
    proc setup() : ck
    proc choose(c:commitment) : coeff list
    proc guess(phii : coeff list, w: witness list) : coeff * coeff
  }.
  

  module Strong_Hiding (S: PC_Scheme, H : PC_Algorithms, A : AdvSH) = {
    
    proc real() : bool = {
      var phi, key; (* The polynomial and commitment scheme key *)
      var c : commitment; (* Commitment to the polynoimal *)
      var i, phii : coeff; (* Adversary's response *)
      var d, js; (* opening to the commitment and list of point evaludated *)
      var phiis : coeff list; (* eval at the points in js *)
      var ws : witness list; (* witness to evaluation *)
      var temp1, temp2, b;
      var j : int;

      phi <$ BasePoly.dpoly t coeff_sample;
      key <@ A.setup();

      b <@ H.valid_key(key);
      
      (c, d) <@ S.commit(key, phi);

      (* construct evaluation points *)
      js <@ A.choose(c);
      phiis <- map (fun x => BasePoly.peval phi x) js;
      
      ws <- [];
      j <- 0;
      while (j < t -1) {
        (temp1, temp2) <@ S.createwitness(key, phi, nth IDCoeff.zeror js j, d);
        ws <- temp2 :: ws;
        j <- j +1;
      }  
      
      (i, phii) <@ A.guess(phiis,ws);

      return (b /\ phii = BasePoly.peval phi i /\ ! i \in js /\ size js = t-1 /\ uniq js);
    }
  }.

end PolynomialCommitment.

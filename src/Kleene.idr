module Kleene

import Poset 

%access public export
%default total

interface Poset t => PointedPoset t where
  bottom : t 
  bottomLeast : (x : t) -> leq bottom x

PointedPoset Nat where
  bottom = Z
  bottomLeast x = LTEZero

approx : PointedPoset t => (t -> t) -> Nat -> t
approx f  Z    = bottom
approx f (S n) = f (approx f n)

lemma3 : PointedPoset t => (f : t -> t) -> (n : Nat) -> monotone f -> leq (approx f n) (approx f (S n)) 
lemma3 f  Z    mf = bottomLeast (f bottom)
lemma3 f (S n) mf = mf (approx f n) (approx f (S n)) (lemma3 f n mf)

lemma4 : PointedPoset t => (f : t -> t) -> (n, m : Nat) -> monotone f -> leq (approx f n) (approx f (n+m)) 
lemma4 f n  Z    mf = rewrite plusZeroRightNeutral n in 
                      leqRefl (approx f n)
lemma4 f n (S m) mf = rewrite plusCommutative n (S m) in 
                      rewrite plusCommutative m n in 
                      leqTrans (approx f n) (f (approx f n)) (f (approx f (n+m))) 
                        (lemma3 f n mf) 
                        (mf (approx f n) (approx f (n+m)) (lemma4 f n m mf))

natDiff : (n, m : Nat) -> (p ** Either (n = m+p) (m = n+p))
natDiff  Z    m = (m ** Right Refl)
natDiff (S n) m = 
  let (p**lr) = natDiff n m in 
  case lr of 
    Left prf => (S p ** Left $ rewrite plusCommutative m (S p) in 
                               rewrite plusCommutative p m in 
                               cong prf)
    Right prf => case p of 
      Z => (1 ** Left $ rewrite prf in 
                        rewrite plusZeroRightNeutral n in 
                        sym $ plusCommutative n 1)
      S p => (p ** Right $ rewrite prf in 
                           rewrite plusCommutative n p in
                           plusCommutative n (S p))
                      
omegaChain : PointedPoset t => (f : t -> t) -> (n, m : Nat) -> monotone f 
                            -> Either (leq (approx f n) (approx f m)) (leq (approx f m) (approx f n))
omegaChain f n m mf = 
  let (p ** prf) = natDiff n m in 
  case prf of 
    Left l => Right $ rewrite l in 
                      case m of 
                        Z => bottomLeast (approx f p)
                        S m => mf (approx f m) (approx f (m+p)) $ lemma4 f m p mf
    Right r => Left $ rewrite r in 
                      case n of 
                        Z => bottomLeast (approx f p)
                        S n => mf (approx f n) (approx f (n+p)) $ lemma4 f n p mf

kleeneChainDirected : PointedPoset t => (f : t -> t) -> monotone f -> directed (\x => (n ** x = approx f n))
kleeneChainDirected f mf = 
  ( (bottom ** Z ** Refl)
  , \x1, x2, (n1 ** eq1), (n2 ** eq2) => 
    rewrite eq1 in 
    rewrite eq2 in
    case omegaChain f n1 n2 mf of 
      Left l  => (approx f n2 ** (l, leqRefl (approx f n2), (n2 ** Refl)))
      Right r => (approx f n1 ** (leqRefl (approx f n1), r, (n1 ** Refl)))
  )

lemma5 : PointedPoset t => (f : t -> t) -> monotone f -> (x : t) -> (n : Nat) -> f x = x -> leq (approx f n) x
lemma5 f mf x  Z    prf = bottomLeast x
lemma5 f mf x (S n) prf = 
  rewrite sym prf in 
  mf (approx f n) x $ lemma5 f mf x n prf

interface PointedPoset t => PDCPoset t where
  directedComplete : (p : t -> Type) -> directed p -> (x ** supremum p x)

posetFromPDC : PDCPoset t -> Poset t 
posetFromPDC pdc = %implementation

kleene : PDCPoset t => (f : t -> t) -> continuous f 
                    -> (x ** (supremum (\x2 => (n ** x2 = approx f n)) x, f x = x, (x2 : t) -> f x2 = x2 -> leq x x2))
kleene @{pdc} f cf = 
  let 
    mf = continuousImpliesMonotone f cf
    dir = kleeneChainDirected f mf
    (x ** sup) = directedComplete (\z => (n ** z = approx f n)) dir  
   in 
    (x ** 
       ( sup
       , let (fxsup, fxuniq) = cf (\z => (n ** z = approx f n)) x dir sup in 
         supremumUniqueness @{posetFromPDC pdc} (\z => (n ** z = approx f n)) (f x) x 
         ( \x2, (n ** prf) => 
           rewrite prf in 
           case n of
             Z => bottomLeast (f x)
             S n => fxsup (approx f (S n)) (approx f n ** ((n ** Refl), Refl)) 
         , \x3, fx3 => 
           fxuniq x3 $ \x4, (x5 ** ((n2 ** prf2), prf5)) => 
           rewrite prf5 in 
           rewrite prf2 in
           fx3 (approx f (S n2)) (S n2 ** Refl)
         )
        sup
       , \x2, prf =>
         (snd sup) x2 $ \x3, (n ** prf2) => 
         rewrite prf2 in
         lemma5 f mf x2 n prf
       )
    )

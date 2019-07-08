module Poset

%access public export
%default partial

interface Poset t where
  leq : t -> t -> Type
  leqRefl : (x : t) -> leq x x
  leqTrans : (x, y, z : t) -> leq x y -> leq y z -> leq x z
  leqAntisym : (x, y : t) -> leq x y -> leq y x -> x = y

lteAntisymmetric : LTE n m -> LTE m n -> n = m
lteAntisymmetric  LTEZero      LTEZero     = Refl
lteAntisymmetric (LTESucc l1) (LTESucc l2) = cong $ lteAntisymmetric l1 l2

Poset Nat where
  leq = LTE 
  leqRefl x = lteRefl
  leqTrans x y z = lteTransitive
  leqAntisym x y = lteAntisymmetric

supremum : Poset t => (t -> Type) -> t -> Type
supremum p x = ((x2 : t) -> p x2 -> leq x2 x, (x3 : t) -> ((x2 : t) -> p x2 -> leq x2 x3) -> leq x x3)

supremumUniqueness : Poset t => (p : t -> Type) -> (x1, x2 : t) -> supremum p x1 -> supremum p x2 -> x1 = x2
supremumUniqueness p x1 x2 (f1,g1) (f2,g2) = leqAntisym x1 x2 (g1 x2 f2) (g2 x1 f1)

directed : Poset t => (t -> Type) -> Type
directed {t} p = (DPair t p, (x1, x2 : t) -> p x1 -> p x2 -> DPair t (\x3 => (leq x1 x3, leq x2 x3, p x3)))

monotone : Poset t => (t -> t) -> Type
monotone {t} f = (x1, x2 : t) -> leq x1 x2 -> leq (f x1) (f x2)

continuous : Poset t => (t -> t) -> Type
continuous {t} f = (p : t -> Type) -> (x1 : t) -> directed p -> supremum p x1 -> supremum (\x2 => (x3 ** (p x3, x2 = f x3))) (f x1)

lemma1 : Poset t => (x1, x2 : t) -> leq x1 x2 -> (x3, x4 : t) -> Either (x3 = x1) (x3 = x2) -> Either (x4 = x1) (x4 = x2) -> (y : t ** (leq x3 y, leq x4 y, Either (y = x1) (y = x2)))
lemma1 x1 x2 leq12 x1 x1 (Left Refl)  (Left Refl)  = (x2 ** (leq12     , leq12     , Right Refl))
lemma1 x1 x2 leq12 x1 x2 (Left Refl)  (Right Refl) = (x2 ** (leq12     , leqRefl x2, Right Refl))
lemma1 x1 x2 leq12 x2 x1 (Right Refl) (Left Refl)  = (x2 ** (leqRefl x2, leq12     , Right Refl))
lemma1 x1 x2 leq12 x2 x2 (Right Refl) (Right Refl) = (x2 ** (leqRefl x2, leqRefl x2, Right Refl))

lemma2 : Poset t => (x1, x2 : t) -> leq x1 x2 -> (x3 : t) -> Either (x3 = x1) (x3 = x2) -> leq x3 x2
lemma2 x1 x2 leq12 x1 (Left  Refl) = leq12
lemma2 x1 x2 leq12 x2 (Right Refl) = leqRefl x2

continuousImpliesMonotone : Poset t => (f : t -> t) -> continuous f -> monotone f
continuousImpliesMonotone f cf x1 x2 leq12 = 
  (fst $ cf (\x => Either (x=x1) (x=x2)) x2 
     ( (x1 ** Left Refl)
     , lemma1 x1 x2 leq12
     ) 
     ( lemma2 x1 x2 leq12
     , \x3, f => f x2 (Right Refl)
     )
  ) 
  (f x1) 
  (x1 ** (Left Refl, Refl))
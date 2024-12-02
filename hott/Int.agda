{-# OPTIONS --without-K --rewriting #-}

open import UTT

open import Agda.Builtin.Nat

module Int where

Int : Type
Int = Nat ⊎ ⊤ ⊎ Nat

one-int : Int
one-int = inr (inr zero)

zero-int : Int
zero-int = inr (inl tt)

minus-one-int : Int
minus-one-int = inl zero

suc-eqv : Int ≃ Int
f suc-eqv (inl (suc m)) = inl m
f suc-eqv (inl zero) = zero-int
f suc-eqv (inr (inl m)) = inr (inr zero)
f suc-eqv (inr (inr m)) = inr (inr (suc m))

g suc-eqv (inl m) = inl (suc m)
g suc-eqv (inr (inl m)) = inl zero
g suc-eqv (inr (inr zero)) = zero-int
g suc-eqv (inr (inr (suc m))) = inr (inr m)

η suc-eqv (inl (suc m)) = refl
η suc-eqv (inl zero) = refl
η suc-eqv (inr (inl tt)) = refl
η suc-eqv (inr (inr zero)) = refl
η suc-eqv (inr (inr (suc m))) = refl

h suc-eqv = g suc-eqv

ε suc-eqv (inl (suc m)) = refl
ε suc-eqv (inl zero) = refl
ε suc-eqv (inr (inl tt)) = refl
ε suc-eqv (inr (inr zero)) = refl
ε suc-eqv (inr (inr (suc m))) = refl


module _ {P : Int -> Type l1} (z* : P zero-int)
         (e* : (m : Int) -> P m ≃ P (f suc-eqv m)) where
  ind-int : (m : Int) -> P m
  ind-int (inl (suc m)) = g (e* (inl (suc m))) (ind-int (inl m))
  ind-int (inl zero) = g (e* minus-one-int) z*
  ind-int (inr (inl tt)) = z*
  ind-int (inr (inr zero)) = f (e* zero-int) z*
  ind-int (inr (inr (suc m))) = f (e* (inr (inr m))) (ind-int (inr (inr m)))

  ind-int-zero : ind-int zero-int ≡ z*
  ind-int-zero = refl

  ind-int-e : (m : Int) -> ind-int (f suc-eqv m) ≡ f (e* m) (ind-int m)
  ind-int-e (inl (suc m)) = ! (ε' (e* (inl (suc m)))
                                  (ind-int (f suc-eqv (inl (suc m)))))
  ind-int-e (inl zero) = ! (ε' (e* minus-one-int) z*)
  ind-int-e (inr (inl tt)) = refl
  ind-int-e (inr (inr zero)) = refl
  ind-int-e (inr (inr (suc m))) = refl


module _ {Y : Type l1} (z* : Y) (e* : Y ≃ Y) where
  rec-int : Int -> Y
  rec-int = ind-int {P = λ _ -> Y} z* (λ _ -> e*)
    
  rec-int-zero : rec-int zero-int ≡ z*
  rec-int-zero = refl

  rec-int-e : (m : Int) -> rec-int (f suc-eqv m) ≡ f e* (rec-int m)
  rec-int-e = ind-int-e z* (λ _ -> e*)

  rec-int-ε : (m : Int) -> rec-int m ≡ f e* (rec-int (g suc-eqv m))
  rec-int-ε m = ap rec-int (! (ε' suc-eqv m)) • rec-int-e (g suc-eqv m)

  rec-int-!e : (m : Int) -> rec-int (g suc-eqv m) ≡ g e* (rec-int m)
  rec-int-!e m = f (adj e*) (! (rec-int-e (g suc-eqv m))) •
                 ap (λ n -> g e* (rec-int n)) (ε' suc-eqv m) 

  rec-int-η : (m : Int) -> rec-int m ≡ g e* (rec-int (f suc-eqv m))
  rec-int-η m = ap rec-int (! (η suc-eqv m)) • rec-int-!e (f suc-eqv m)



nat-has-dec-eq : has-dec-eq Nat
nat-has-dec-eq zero zero = inl refl
nat-has-dec-eq zero (suc n) = inr (λ ())
nat-has-dec-eq (suc m) zero = inr (λ ())
nat-has-dec-eq (suc m) (suc n) = aux (nat-has-dec-eq m n)
  module nat-has-dec-eq where
  aux : is-dec (m ≡ n) → is-dec (suc m ≡ suc n)
  aux (inl e) = inl (ap suc e)
  aux (inr a) = inr (λ e → a (ap (λ m → m - 1) e))

module _ {X1 : Type l1} {X2 : Type l2} where

  code : X1 ⊎ X2 -> X1 ⊎ X2 -> Type (l1 ⊔ l2)
  code (inl x) (inl x') = Lift {l1} {l2} ( x ≡ x' )
  code (inl x) (inr y)  = ⊥
  code (inr y) (inl x)  = ⊥
  code (inr y) (inr y') = Lift {l2} {l1} ( y ≡ y' )

  r : (a : X1 ⊎ X2) -> code a a
  r (inl x) = lift (refl)
  r (inr y) = lift (refl)

  enc : (a b : X1 ⊎ X2) -> a ≡ b -> code a b
  enc a b p = tpt (code a) p (r a)

  dec : (a b : X1 ⊎ X2) -> code a b -> a ≡ b
  dec (inl x) (inl x') p = ap inl (UTT.Lift.lower p)
  dec (inl x) (inr y)  a = rec⊥ a
  dec (inr y) (inl x)  a = rec⊥ a
  dec (inr y) (inr y') p = ap inr (UTT.Lift.lower p)


  inl-inj : {x11 x12 : X1} → inl {X = X1} {Y = X2} x11 ≡ inl x12 → x11 ≡ x12
  inl-inj refl = refl

  inr-inj : {x21 x22 : X2} → inr {X = X1} {Y = X2} x21 ≡ inr x22 → x21 ≡ x22
  inr-inj refl = refl

  lem1 : {x11 x12 : X1} → is-dec (x11 ≡ x12) → is-dec (inl x11 ≡ inl x12)
  lem1 (inl x) = inl (ap inl x)
  lem1 (inr x) =  inr (λ p → rec⊥ (x (inl-inj p)))

  lem2 : {x21 x22 : X2} -> is-dec (x21 ≡ x22) → is-dec (inr x21 ≡ inr x22)
  lem2 {x21} {x22} (inl x) = inl (ap inr x)
  lem2 {x21} {x22} (inr x) = inr (λ p → rec⊥ (x (inr-inj p)))


  coprod-dec-eq : has-dec-eq X1 → has-dec-eq X2 → has-dec-eq (X1 ⊎ X2)
  coprod-dec-eq a1 a2 (inl x11) (inl x12) = lem1 (a1 x11 x12)
  coprod-dec-eq a1 a2 (inl x1)  (inr x2)  = inr λ p → enc (inl x1) (inr x2) p
  coprod-dec-eq a1 a2 (inr x2)  (inl x1)  = inr λ p → enc (inr x2) (inl x1) p
  coprod-dec-eq a1 a2 (inr x21) (inr x22) = lem2 (a2 x21 x22)


int-is-set : is-set Int
int-is-set = has-dec-eq->is-set
               (coprod-dec-eq
                  nat-has-dec-eq
                  (coprod-dec-eq
                   (λ { tt tt → inl refl })
                   nat-has-dec-eq))

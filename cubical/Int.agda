{-# OPTIONS --cubical #-}

open import Common
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

sucInt : Int → Int
sucInt (inl zero) = inr (inl tt)
sucInt (inl (suc x)) = inl x
sucInt (inr (inl x)) = inr (inr zero)
sucInt (inr (inr x)) = inr (inr (suc x))

predInt : Int → Int
predInt (inl x) = inl (suc x)
predInt (inr (inl x)) = inl zero
predInt (inr (inr zero)) = inr (inl tt)
predInt (inr (inr (suc x))) = inr (inr x)

ϵ : (y : Int) → sucInt(predInt y) ≡ y
ϵ (inl x) = refl
ϵ (inr (inl tt)) = refl
ϵ (inr (inr zero)) = refl
ϵ (inr (inr (suc x))) = refl

η : (y : Int) → predInt(sucInt y) ≡ y
η (inl zero) = refl
η (inl (suc x)) = refl
η (inr (inl tt)) = refl
η (inr (inr x)) = refl

lemma : (x : Int) → (y : fiber sucInt x) → (predInt x , ϵ x) ≡ y
lemma x (y , p) = λ i ->  {!!} , {!!}

-- (ap predInt p)
-- i = 0 -> predInt (sucInt y)
-- i = 1 -> predInt x
-- η y
-- i = 0 -> predInt ( sucInt (x) ) = x
-- i = 1


-- lemma (inl zero) (inl zero , p) = rec⊥ (inl-neq-inr (! p))
-- lemma (inl (suc x)) (inl zero , p) = rec⊥ (inl-neq-inr (! p))
-- lemma (inl x) (inl (suc y) , p) = λ i →   inl (suc ((! (inl-eq p) ) i) ) , {!!}
-- -- λ j → {! p ((~ i ∨ j) ∨ j)!}
-- -- {!!} {!!}
-- -- {! p ((~ i ∨ j) ∨ j)!}
-- lemma (inl x) (inr y , p) = {!!}
-- lemma (inr x) y = {!!}

suc-eqv : Int ≃ Int
suc-eqv .fst = sucInt
suc-eqv .snd .equiv-proof x = ((predInt x) , ϵ x), lemma x

-- module _ {P : Int -> Type l1} (z* : P zero-int)
--          (e* : (m : Int) -> P m ≃ P (f suc-eqv m)) where
--   ind-int : (m : Int) -> P m
--   ind-int (inl (suc m)) = g (e* (inl (suc m))) (ind-int (inl m))
--   ind-int (inl zero) = g (e* minus-one-int) z*
--   ind-int (inr (inl tt)) = z*
--   ind-int (inr (inr zero)) = f (e* zero-int) z*
--   ind-int (inr (inr (suc m))) = f (e* (inr (inr m))) (ind-int (inr (inr m)))

--   ind-int-zero : ind-int zero-int ≡ z*
--   ind-int-zero = refl

--   ind-int-e : (m : Int) -> ind-int (f suc-eqv m) ≡ f (e* m) (ind-int m)
--   ind-int-e (inl (suc m)) = ! (ε' (e* (inl (suc m)))
--                                   (ind-int (f suc-eqv (inl (suc m)))))
--   ind-int-e (inl zero) = ! (ε' (e* minus-one-int) z*)
--   ind-int-e (inr (inl tt)) = refl
--   ind-int-e (inr (inr zero)) = refl
--   ind-int-e (inr (inr (suc m))) = refl


-- module _ {Y : Type l1} (z* : Y) (e* : Y ≃ Y) where
--   rec-int : Int -> Y
--   rec-int = ind-int {P = λ _ -> Y} z* (λ _ -> e*)

--   rec-int-zero : rec-int zero-int ≡ z*
--   rec-int-zero = refl

--   rec-int-e : (m : Int) -> rec-int (f suc-eqv m) ≡ f e* (rec-int m)
--   rec-int-e = ind-int-e z* (λ _ -> e*)

--   rec-int-ε : (m : Int) -> rec-int m ≡ f e* (rec-int (g suc-eqv m))
--   rec-int-ε m = ap rec-int (! (ε' suc-eqv m)) • rec-int-e (g suc-eqv m)

--   rec-int-!e : (m : Int) -> rec-int (g suc-eqv m) ≡ g e* (rec-int m)
--   rec-int-!e m = f (adj e*) (! (rec-int-e (g suc-eqv m))) •
--                  ap (λ n -> g e* (rec-int n)) (ε' suc-eqv m)

--   rec-int-η : (m : Int) -> rec-int m ≡ g e* (rec-int (f suc-eqv m))
--   rec-int-η m = ap rec-int (! (η suc-eqv m)) • rec-int-!e (f suc-eqv m)



-- nat-has-dec-eq : has-dec-eq Nat
-- nat-has-dec-eq zero zero = inl refl
-- nat-has-dec-eq zero (suc n) = inr (λ ())
-- nat-has-dec-eq (suc m) zero = inr (λ ())
-- nat-has-dec-eq (suc m) (suc n) = aux (nat-has-dec-eq m n)
--   module nat-has-dec-eq where
--   aux : is-dec (m ≡ n) → is-dec (suc m ≡ suc n)
--   aux (inl e) = inl (ap suc e)
--   aux (inr a) = inr (λ e → a (ap (λ m → m - 1) e))

-- module _ {X1 X2 : Type l1} where
--   coprod-dec-eq : has-dec-eq X1 → has-dec-eq X2 → has-dec-eq (X1 ⊎ X2)
--   coprod-dec-eq a1 a2 (inl x11) (inl x12) = aux (a1 x11 x12)
--     module coprod-dec-eq-inl where
--     aux : is-dec (x11 ≡ x12) → is-dec (inl x11 ≡ inl x12)
--     aux (inl e) = inl (ap inl e)
--     aux (inr a) = inr (λ e → a (inl-eq e))
--   coprod-dec-eq a1 a2 (inl x1)  (inr x2)  = inr inl-neq-inr
--   coprod-dec-eq a1 a2 (inr x2)  (inl x1)  = inr (λ e → inl-neq-inr (! e))
--   coprod-dec-eq a1 a2 (inr x21) (inr x22) = aux (a2 x21 x22)
--     module coprod-dec-eq-inr where
--     aux : is-dec (x21 ≡ x22) → is-dec (inr x21 ≡ inr x22)
--     aux (inl e) = inl (ap inr e)
--     aux (inr a) = inr (λ e → a (inr-eq e))

-- int-is-set : is-set Int
-- int-is-set = has-dec-eq->is-set
--                (coprod-dec-eq
--                   nat-has-dec-eq
--                   (coprod-dec-eq
--                    (λ { tt tt → inl refl })
--                    nat-has-dec-eq))

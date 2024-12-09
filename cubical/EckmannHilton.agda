{-# OPTIONS --cubical #-}

open import Common
open import Agda.Builtin.Nat


module EckmannHilton where

refl-right-unital : {l : Level} {A : Type l} {x y : A} → (p : x ≡ y) →  pathComp p refl ≡ p
refl-right-unital {A = A} {x = x} {y = y} p j i = hfill (λ _ → λ { (i = i0) → x
                                                    ; (i = i1) → y })
                                           (inS (p i))
                                           (~ j)

refl-left-unital :  {l : Level} {A : Type l} {x y : A} → (p : x ≡ y) →  pathComp refl p ≡ p
refl-left-unital {A = A} {x = x} {y = y} p = J x (λ y p → pathComp refl p ≡ p) (refl-right-unital refl) y p

inverse-right-cancel : {l : Level} {A : Type l} {x y : A} → (p : x ≡ y) →  pathComp p (! p) ≡ refl
inverse-right-cancel {x = x} {y = y} p = J x (λ y p → pathComp p (! p) ≡ refl) (refl-left-unital refl) y p

inverse-left-cancel : {l : Level} {A : Type l} {x y : A} → (p : x ≡ y) →  pathComp (! p) p ≡ refl
inverse-left-cancel {y = y} p = J _ (λ y p → pathComp (! p) p ≡ refl) (refl-right-unital refl) y p

assoc : {l : Level} {A : Type l} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
        → pathComp p (pathComp q r) ≡ pathComp (pathComp p q) r
assoc {z = z} {w = w} p q r = J z (λ y p' → pathComp p (pathComp q p') ≡ pathComp (pathComp p q) p') (pathComp l1 (! l2)) w r
  where
    l1 : pathComp p (pathComp q refl) ≡ pathComp p q
    l1 i = pathComp p ( ( refl-right-unital q ) i )

    l2 : pathComp (pathComp p q) refl ≡ pathComp p q
    l2 =  refl-right-unital (pathComp p q)

-- Ω2 : {l : Level} {A : Type l} {a : A} → refl ≡ refl
-- Ω2 = {!refl!}

-- infixr 8 _•l_
-- _•l_ : {l : Level} {A : Type l} {x y z : A} → {p q : x ≡ y} (α : p ≡ q) → (r : y ≡ z) → pathComp p r ≡ pathComp q r
-- (α •l r) = J {!_!} (λ y q' → {!!}) {!!} {!!} {!!}

-- eckman-hilton : {l : Level} {A : Type l} {a : A} (α : refl {x = a} ≡ refl) → (β : refl ≡ refl) → pathComp α β ≡ pathComp β α
-- eckman-hilton α β  = {!!}

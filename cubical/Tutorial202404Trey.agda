{-# OPTIONS --without-K --no-import-sorts --rewriting --allow-unsolved-metas #-}
module Tutorial202404Trey where

open import Agda.Primitive renaming (Set to Type) public

infixr 4 _≡_
data _≡_ {l : Level} {X : Type l} (x1 : X) : (x2 : X) -> Type l where
  refl : x1 ≡ x1

{-# BUILTIN REWRITE _≡_ #-}

ap : {X Y : Type} -> (f : X -> Y) -> {x1 x2 : X} -> (p : x1 ≡ x2) -> f x1 ≡ f x2
ap f refl = refl

tpt : {X : Type} -> (P : X -> Type) -> {x1 x2 : X} -> (p : x1 ≡ x2) -> P x1 -> P x2
tpt P refl p = p

apd : {X : Type} -> (P : X -> Type) -> (f : (x : X) -> P x) -> {x1 x2 : X} -> (p : x1 ≡ x2) ->
      tpt P p (f x1) ≡ f x2
apd P f refl = refl

infixr 8 _•_
_•_ : {X : Type} -> {x1 x2 x3 : X} -> (p : x1 ≡ x2) -> (q : x2 ≡ x3) -> x1 ≡ x3
p • refl = p

infix 10 !
! : {X : Type} -> {x1 x2 : X} -> (p : x1 ≡ x2) -> x2 ≡ x1
! refl = refl

infixr 5 _⊎_
data _⊎_ (X : Type) (Y : Type) : Type where
  inl : X -> X ⊎ Y
  inr : Y -> X ⊎ Y

infix 4 _≃_
record _≃_ (X : Type) (Y : Type) : Type where
  constructor biinv
  field
    f : X -> Y
    g : Y -> X
    η : (x : X) → g (f x) ≡ x
    h : Y -> X
    ϵ : (y : Y) → f (h y) ≡ y
open _≃_ public

module _ {X : Type} {Y : Type} (e : X ≃ Y) where
  -- f is a left inverse of g
  ϵ' : (y : Y) → f e (g e y) ≡ y
  ϵ' y = ! (ap (λ y → f e (g e y)) (ϵ e y)) • ap (f e) (η e (h e y)) • ϵ e y
  -- Define η'
  -- h is a left inverse of f
  η' : (x : X) →  h e (f e x) ≡ x
  η' x =  !(η e (h e (f e x))) • ap (g e) (ϵ e (f e x)) • η e x
  --  ap (h e) (ϵ' (f e x))
  τ' : (x : X) -> ap (f e) (η e x) ≡ ϵ' (f e x)
  τ' x = {!!}

postulate
  Z : Type
  zero : Z
  e : Z ≃ Z

module _ {P : Z -> Type} (z* : P zero)
         (e* : (m : Z) → P m ≃ P (f e m)) where

  postulate
    indZ : (m : Z) -> P m
    indZ-zero : indZ zero ≡ z*
  {-# REWRITE indZ-zero #-}

  postulate
    indZ-e : (m : Z) -> indZ (f e m) ≡ f (e* m) (indZ m)



module Recursion where
  module _ {Y : Type} (z* : Y) (e* : Y ≃ Y) where
    recZ : Z -> Y
    recZ = indZ {P = λ _ -> Y} z* (λ _ -> e*)

    recZ-zero : recZ zero ≡ z*
    recZ-zero = refl

    recZ-e : (m : Z) -> recZ (f e m) ≡ f e* (recZ m)
    recZ-e m = indZ-e z* (λ m → e*) m

    recZ-ϵ : (m : Z) -> recZ m ≡ f e* (recZ (g e m))
    recZ-ϵ m = ! (ap (λ m → recZ m) (ϵ' e m)) • recZ-e (g e m)

    recZ-!e : (m : Z) -> recZ (g e m) ≡ g e* (recZ m)
    recZ-!e m = !(η e* (recZ (g e m))) • ap (g e*) (!(recZ-e (g e m))) • ap (g e*) (ap recZ (ϵ' e m))

    recZ-η : (m : Z) -> recZ m ≡ g e* (recZ (f e m))
    recZ-η m = !(ap (λ m → recZ m) (η e m)) • recZ-!e (f e m)

postulate
  S1 : Type
  base : S1 -- basepoint
  loop : base ≡ base -- path from base to base that is not refl, this is what makes HIT

-- postulate
--    ind-S1 : (P : S1 → Type) → (


-- A ≡ B implies A ≃ B

module _ {A : Type} {B : Type} where
  path-to-equiv : A ≡ B → A ≃ B
  f (path-to-equiv refl) a = a
  g (path-to-equiv refl) b = b
  η (path-to-equiv refl) x = refl
  h (path-to-equiv refl) a = a
  ϵ (path-to-equiv refl) y = refl

-- equivalence from Z to N + N


data Nat : Type where
  z : Nat
  suc : Nat -> Nat

data Unit : Type where
  ⋆ : Unit

-- module _ where
--   equiv : Z ≃ Int
--   f equiv = {!recZ z* e* where
--             z* : Nat ⊎ Unit ⊎ Nat
--             z* = ?
--             e* : Nat ⊎ Unit ⊎ Nat ≃ Nat ⊎ Unit ⊎ Nat
--             e* = ?!}
--   g equiv = {!!}
--   η equiv = {!!}
--   h equiv = {!!}
--   ϵ equiv = {!!}
-- use recursion principle in both directions
-- use induction to show round trips are the same thing

-- P zero P x P succ x
-- zero x succ x
-- indZ : (P : Z -> Type) -> (P zero) -> (x : X) -> (P x) ≃ (P succ x) ->
-- (x : Z ) → P x
-- ind-S1 : (P : S1 → Type) → (b* : P base) → (x : S1) → (loop* : tpt P loop base* ≡ base*)
-- → (x : S1 ) → P x
-- seperate loop & refl via the induction principle on S1

tpt-const : {X : Type} → {Y : Type } →  {x1 x2 : X} →  (e : x1 ≡ x2) →  (y1 : Y) → tpt (λ _ → Y) e y1 ≡ y1
tpt-const refl y1 = refl

-- apd-const :

postulate
  ind-S1 : (P : S1 -> Type) → (b* : P base) → (loop* : tpt P loop b* ≡ b*)
           → (x : S1 ) → P x

postulate
  ind-S1-base : (P : S1 → Type) -> (base* : P base) → (loop* : tpt P loop base* ≡ base*)
               → (ind-S1 P base* loop*) base ≡ base*

{-# REWRITE ind-S1-base #-}

postulate
  ind-S1-loop : (P : S1 → Type) → (base* : P base) → (loop* : tpt P loop base* ≡ base*)
                → apd P (ind-S1 P base* loop*) loop ≡ loop*


postulate
  Circle : Type
  ze one : Circle
  north-path : ze ≡ one
  south-path : ze ≡ one

-- induction & computational principle for this
-- S1 ≃ Circle
-- two circles: one which is subdivided and one which isnt

rec-S1 : (X : Type) → (base* : X) → (loop* : base* ≡ base*) → (S1 → X)
rec-S1 X base* loop* x = ind-S1 ((λ _ → X)) base* (tpt-const loop base* • loop*) x

rec-S1-base : (X : Type) → (base* : X) → (loop* : base* ≡ base*) →
              rec-S1 X base* loop* base ≡ base*
rec-S1-base = {!!}

rec-S1-loop : (X : Type) → (base* : X) → (loop* : base* ≡ base*) →
              ap (rec-S1 X base* loop*) loop ≡ loop*
rec-S1-loop X base* loop* = {!!}
-- Ind-s1-loop (λ _ → X) (base*) (tpt-const loop base* • loop*)
-- apd-const lemma - to ap
-- lemma path alg p • q ≡ p • r -> q ≡ r
-- s • !n

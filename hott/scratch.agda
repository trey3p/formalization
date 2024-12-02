{-# OPTIONS --without-K --no-import-sorts --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive renaming (Set to Type) public

infixr 4 _≡_
data _≡_ {X : Type} (x1 : X) : (x2 : X) -> Type where
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
    f : X → Y
    g : Y → X
    η : (x : X) → g (f x) ≡ x
    h : Y → X
    ϵ : (y : Y) → f (h y) ≡ y

open _≃_ public

data Unit : Type where
  ⋆ : Unit

module _ {X : Type} {Y : Type} (e : X ≃ Y) where

  ϵ' : (y : Y) → f e (g e y) ≡ y
  ϵ' y = ! (ap (λ y → f e ( g e y))(ϵ e y)) • ap (f e) (η e (h e y)) • ϵ e y


postulate
  ∀-extensionality : ∀ {A : Type} {B : A → Type} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

module ≃-Unit-fun {A : Type} where
    to : A → (Unit → A)
    to a _ = a

    from1 : (Unit → A) → A
    from1 f = f ⋆

    from-to : (a : A) → from1 (to a) ≡ a
    from-to a = refl

    from2 : (Unit → A) → A
    from2 f = f ⋆

    to-from : (f : Unit → A) → to (from2 f) ≡ f
    to-from f = ∀-extensionality λ{ ⋆ → refl}

    Unit→A≃A : A ≃ (Unit → A)
    Unit→A≃A = biinv to from1 from-to from2 to-from

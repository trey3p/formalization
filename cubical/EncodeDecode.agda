{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Core.Primitives
open import Cubical.Core.Glue
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit


module _ where

data ⊥ {ℓ} : Type ℓ where

infixr 5 _⊎_
data _⊎_ {ℓ ℓ'} (X : Type ℓ) (Y : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : X -> X ⊎ Y
  inr : Y -> X ⊎ Y

module _ {ℓ : Level} where

-- primTransp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (a : A i0) → A i1
-- primitive transport says if I have a line of types and a term at the type on the 0 end, I can give you a term of the type on the 1 end.


  coe : {X Y : Type ℓ} -> Path _ X Y -> X -> Y
  coe p = transp (λ i → p i) i0

-- coe says that if I have a path between two types in the same universe, I can give you a function between those types

module _ {ℓ ℓ' : Level} where
  ap : {X : Type ℓ} -> {Y : Type ℓ'} -> (f : X -> Y) -> {x1 x2 : X} ->
       Path X x1 x2 -> Path Y (f x1) (f x2)
  ap f p i = f (p i)

module _ {ℓ ℓ' : Level} where
  tpt : {X : Type ℓ} -> (P : X -> Type ℓ') -> {x1 x2 : X} ->
        Path X x1 x2 -> P x1 -> P x2
  tpt P p = coe (ap P p)


-- tpt says that if I have a path between two elements and a type family over the type of my elements, I can give you a function from the type family at the 0 end element to the type family at the 1 end element.
refl : ∀ {ℓ} { X : Type ℓ } {x : X} → x ≡ x
refl {x = x} = λ i → x


tpt-refl : ∀ { ℓ ℓ' } (X : Type ℓ) → {x : X} → (P : X → Type ℓ') → (u : P x) → tpt P (refl) u ≡ u
tpt-refl X {x = x } P u i = transp (λ _ → P x) i u



module _ {ℓ ℓ' : Level} {X : Type ℓ} (x0 : X) where
  coed : (P : (x : X) → Path X x0 x → Type ℓ') ->
         {x1 : X} → (p : Path X x0 x1) →
         PathP _ (P x0 (λ i → x0)) (P x1 p) ->
         P x0 (λ i → x0) -> P x1 p
  coed P p q = transp (λ i → q i) i0

module _ {ℓ ℓ' : Level} {X : Type ℓ} where
  apd : (P : X → Type ℓ') ->
        (f : (x : X) -> P x) ->
        {x1 x2 : X} -> (p : Path X x1 x2) ->
        PathP (λ i -> P (p i)) (f x1) (f x2)
  apd P f p i = f (p i)

module _ {ℓ ℓ' : Level} {X : Type ℓ} (x0 : X) where
  J : (P : (x : X) -> Path X x0 x -> Type ℓ') ->
      (r : P x0 (λ _ -> x0)) ->
      (x1 : X) -> (p : Path X x0 x1) -> P x1 p
  J P r x1 p = coed x0 P p (λ i → P (p i) (λ j → p (i ∧ j))) r



module BoolEncDec where
  code : Bool -> Bool -> Type
  code false false = ⊤
  code false true = ⊥
  code true false = ⊥
  code true true = ⊤

  r : (b : Bool) -> code b b
  r false = tt
  r true = tt

  enc : (b0 b1 : Bool) -> Path _ b0 b1 -> code b0 b1
  enc b0 b1 p = tpt (code b0) p (r b0)

  dec : (b0 b1 : Bool) -> code b0 b1 -> Path _ b0 b1
  dec false false _ _ = false
  dec true true _ _ = true

  enc-η : {b0 b1 : Bool} -> (p : Path _ b0 b1) ->
          Path _ (dec b0 b1 (enc b0 b1 p)) p
  enc-η {false} {b1} =
    J false (λ b p → Path _ (dec false b (enc false b p)) p) (λ i j → false) b1
  enc-η {true} {b1} =
    J true (λ b p → Path _ (dec true b (enc true b p)) p) (λ i j → true) b1
  enc-ϵ : {b0 b1 : Bool} -> (c : code b0 b1) ->
          Path _ (enc b0 b1 (dec b0 b1 c)) c
  enc-ϵ {false} {false} tt _ = tt
  enc-ϵ {true} {true} tt _ = tt


module EqualityInCoproduct {ℓ} {X Y : Type ℓ} where
  code : X ⊎ Y -> X ⊎ Y -> Type ℓ
  code (inl x0) (inl x1) = Path X x0 x1
  code (inl x0) (inr y1) = ⊥
  code (inr y0) (inl x1) = ⊥
  code (inr y0) (inr y1) = Path Y y0 y1

  r : (w : X ⊎ Y) → code w w
  r (inl x) i = x
  r (inr y) i = y

  enc : (w0 w1 : X ⊎ Y) -> Path _ w0 w1 -> code w0 w1
  enc w0 = J w0 (λ w _ → code w0 w) (r w0)

  lem : (x : X) -> Path _ (enc (inl x) (inl x) (λ _ → inl x)) (λ i -> x)
  lem x i = transp (λ _ -> x ≡ x) i (λ i -> x)

  lem2 : (y : Y) → Path _ (enc (inr y) (inr y) (λ _ → inr y)) (λ i → y)
  lem2 y i = transp (λ _ → y ≡ y) i (λ i → y)

  dec : (w0 w1 : X ⊎ Y) -> code w0 w1 -> Path _ w0 w1
  dec (inl x0) (inl x1) p i = inl (p i)
  dec (inr y0) (inr x1) p i = inr (p i)


  enc-η : {w0 w1 : X ⊎ Y} -> (p : Path _ w0 w1) -> Path _ (dec _ _ (enc w0 w1 p)) p
  enc-η {inl x0} {w1} =
    J _
      (λ w p -> Path _ (dec _ _ (enc _ w p)) p)
      (λ i j -> inl (lem x0 i j))
      w1

  enc-η {inr y0} {w1} = J _ (λ w p → Path _ (dec _ _ (enc _ w p)) p) (λ i j → inr (lem2 y0 i j)) w1



  enc-ϵ : (w0 w1 : X ⊎ Y) → (c : code w0 w1) -> Path _ (enc w0 w1 (dec w0 w1 c)) c
  enc-ϵ (inl w0) (inl w1) c =  J _ (λ x p → Path _ (transp (λ i → w0 ≡ p i) i0 (λ i → w0)) p )  (tpt-refl X {x = w0} (λ _ → w0 ≡ w0) refl) w1 c
  enc-ϵ (inr w0) (inr w1) c = J _ (λ x p → Path _ (transp (λ i → w0 ≡ p i) i0 (λ i → w0)) p) (tpt-refl Y {x = w0} (λ y → w0 ≡ w0) refl) w1 c


module _ {X Y : Type} where
  open EqualityInCoproduct

  inl-eq : {x1 x2 : X} -> inl {Y = Y} x1 ≡ inl x2 -> x1 ≡ x2
  inl-eq {x1} {x2} p q = enc (inl x1) (inl x2) p q

  inr-eq : {y1 y2 : Y} -> inr {X = X} y1 ≡ inr y2 -> y1 ≡ y2
  inr-eq {y1} {y2} p = enc (inr y1) (inr y2) p

  inl-neq-inr : {x : X} → {y : Y} -> inl x ≡ inr y → ⊥
  inl-neq-inr {x} {y} p = enc (inl x) (inr y) p


-- dec-eq : {X : Type} -> (x1 x2 : X) -> (x1 ≡ x2) ⊎ (x1 ≡ x2 -> ⊥)
-- dec-eq {X} x1 x2 = {!!}

has-dec-eq : (X : Type) -> Type
has-dec-eq X = (x1 x2 : X) -> (x1 ≡ x2) ⊎ (x1 ≡ x2 -> ⊥)

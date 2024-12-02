{-# OPTIONS --without-K --rewriting #-}
module S1 where

open import UTT
{-# BUILTIN REWRITE _≡_ #-}

postulate
  S1 : Type
  b : S1
  l : b ≡ b

postulate
  ind-s1 : (P : S1 -> Type l1) -> (b* : P b) -> (l* : tpt P l b* ≡ b*) ->
           (x : S1) -> P x

postulate
  ind-s1-b : (P : S1 -> Type l1) -> (b* : P b) -> (l* : tpt P l b* ≡ b*) ->
             ind-s1 P b* l* b ≡ b*
{-# REWRITE ind-s1-b #-}

postulate
  ind-s1-l : (P : S1 -> Type l1) -> (b* : P b) -> (l* : tpt P l b* ≡ b*) ->
             apd P (ind-s1 P b* l*) l ≡ l*


postulate
  rec-s1 : (X : Type l1) -> (b* : X) -> (l* : b* ≡ b*) ->
           (x : S1) -> X

postulate
  rec-s1-b : (X : Type l1) -> (b* : X) -> (l* : b* ≡ b*) ->
             rec-s1 X b* l* b ≡ b*
{-# REWRITE rec-s1-b #-}

postulate
  rec-s1-l : (X : Type l1) -> (b* : X) -> (l* : b* ≡ b*) ->
             ap (rec-s1 X b* l*) l ≡ l*

module _ {X : Type l1} (e : X ≃ X) where
  tpt-rec-s1-l : tpt (rec-s1 (Type l1) X (ua e)) l ≡ f e
  tpt-rec-s1-l =
    tpt-coe-ap _ l •
    ap (tpt (λ X → X)) (rec-s1-l (Type l1) X (ua e)) •
    tpt-id-ua e

  tpt-rec-s1-!l : tpt (rec-s1 (Type l1) X (ua e)) (! l) ≡ g e
  tpt-rec-s1-!l =
    tpt-coe-ap _ (! l) •
    ap (tpt (λ X → X)) (ap-! (rec-s1 (Type l1) X (ua e)) l) •
    ap (λ e → tpt (λ X → X) (! e)) (rec-s1-l (Type l1) X (ua e)) •
    tpt-id-!-ua e

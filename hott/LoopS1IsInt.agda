{-# OPTIONS --without-K --rewriting #-}
module _ where

open import UTT
open import S1
open import Int




code : S1 → Type
code = rec-s1 Type Int (ua suc-eqv)

r : code b
r = zero-int

enc : (a : S1) → (b ≡ a) → code a
enc a e = tpt code e r

dec : (a : S1) → code a → (b ≡ a)
dec = ind-s1 (λ a → code a → (b ≡ a)) b* l*
  module dec where
  b* : code b → b ≡ b
  b* = rec-int refl (rcomp-eqv l)

  aux1 : (m : code b) →
         tpt (λ a → b ≡ a) l (b* (tpt code (! l) m)) ≡ b* m
  aux1 m = tpt-const-eq-var l (b* (tpt code (! l) m)) •
           ap (λ s → b* (s m) • l) (tpt-rec-s1-!l suc-eqv) •
           ap (λ e → e • l) (rec-int-!e refl (rcomp-eqv l) m) •
           •assoc • ap (λ e → b* m • e) •invl •
           •unitr

  l* : tpt (λ a → code a → b ≡ a) l b* ≡ b*
  l* = funext (λ m → tpt-fn l b* m • aux1 m)

enc-η : (a : S1) → (e : b ≡ a) → dec a (enc a e) ≡ e
enc-η _ refl = refl

enc-ε : (a : S1) → (m : code a) → enc a (dec a m) ≡ m
enc-ε = ind-s1 (λ a → (m : code a) → enc a (dec a m) ≡ m) b* l*
  module enc-ε where
  aux : (m : Int) →
        (enc b (dec b m) ≡ m) ≃ (enc b (dec b (f suc-eqv m)) ≡ f suc-eqv m)
  aux m = lcomp-eqv (ap (enc b) (rec-int-e refl (rcomp-eqv l) m) •
                     tpt-comp _ (dec b m) l •
                     f happly-eqv (tpt-rec-s1-l suc-eqv) (enc b (dec b m)))
          ∘e embed suc-eqv
  
  b* : (m : code b) → enc b (dec b m) ≡ m
  b* = ind-int refl aux

  l* : tpt (λ a → (m : code a) → enc a (dec a m) ≡ m) l b* ≡ b*
  l* = funext (λ m → int-is-set _ _)

thm : (a : S1) → (b ≡ a) ≃ code a
f (thm a) = enc a
g (thm a) = dec a
η (thm a) = enc-η a
h (thm a) = g (thm a)
ε (thm a) = enc-ε a

cor : (b ≡ b) ≃ Int
cor = thm b

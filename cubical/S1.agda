{-# OPTIONS --cubical #-}

open import Common
open import Agda.Builtin.Nat
open import Int
open import Cubical.Foundations.Univalence using (ua; ua→)
open import EckmannHilton
module S1 where

data S1 : Type where
  base : S1
  loop : base ≡ base

code : S1 → Type
code base = Int
code (loop i) = (ua suc-eqv ) i

encode : (x : S1) → base ≡ x → code x
encode = J base (λ x _ → code x) (inr (inl tt))

one : Int
one = encode (base) loop

oneisone : one ≡ inr(inr(zero))
oneisone = refl

two : Int
two = encode (base) (loop • loop)

twoistwo : two ≡ sucInt ( one)
twoistwo = refl

decode-base : code base → base ≡ base
decode-base (inl zero) = ! loop
decode-base (inl (suc x)) = decode-base (inl x) • (! loop)
decode-base (inr (inl tt)) = refl
decode-base (inr (inr zero)) = loop
decode-base (inr (inr (suc x))) = decode-base (inr (inr x)) • loop

decode-loop :  PathP (λ i → code (loop i) → (base ≡ loop i ) ) (decode-base) (decode-base)
decode-loop = ua→ ( λ a → helper a )
  where
    A : I → Type
    A = λ i → base ≡ loop i
    helper : (a : Nat ⊎ ⊤ ⊎ Nat) → PathP (λ i → base ≡ loop i) (decode-base a) (decode-base (sucInt a))
    helper (inl zero) = Path-to-PathP A (decode-base (inl zero)) (decode-base (inr (inl tt))) (((tpt-in-iden) ((decode-base (inl zero)) ) (loop) ) • invl loop)
    helper (inl (suc x)) = Path-to-PathP A (decode-base (inl x) • ! loop)
                            (decode-base (inl x)) ((tpt-in-iden (decode-base (inl x) • ! loop)  loop) • (!( assoc (decode-base (inl x)) (! loop) (loop))) • ap (λ p → pathComp (decode-base (inl x)) p) (invl loop) • ! unitr (decode-base (inl x)) )
    helper (inr (inl tt)) = Path-to-PathP A refl loop (tpt-in-iden (refl) loop • ! (unitl loop))
    helper (inr (inr zero)) = Path-to-PathP A loop (loop • loop) ((tpt-in-iden loop loop))
    helper (inr (inr (suc x))) = Path-to-PathP A (decode-base (inr (inr x)) • loop)
                                  ((decode-base (inr (inr x)) • loop) • loop) (tpt-in-iden (decode-base (inr (inr x)) • loop)  loop)

decode : (x : S1) → code x → base ≡ x
decode base = decode-base
decode (loop i) = decode-loop i

enc-η : (a : S1) → (e : base ≡ a) → decode a (encode a e) ≡ e
enc-η a e = J base (λ x p →  decode x (encode x p) ≡ p) refl a e

enc-ϵ : (a : S1) → (m : code a) → encode a (decode a m) ≡ m
enc-ϵ = {!!}

thm : (a : S1) → (base ≡ a) ≃ code a
thm = {!!}

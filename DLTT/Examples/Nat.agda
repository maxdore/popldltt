{-# OPTIONS --safe #-}

module DLTT.Examples.Nat where

open import DLTT.Base
open import DLTT.Function

open import DLTT.Examples.Sum

private
  variable
    ℓ ℓ' : Level



ℕᵒsh : 𝟚ᵒ {ℓ} ． → ltyp ℓ
ℕᵒsh false = 𝟘ᵒ
ℕᵒsh true = 𝟙ᵒ

ℕᵒpos : (x : 𝟚ᵒ {ℓ} ．) → List (ℕᵒsh x ．)
ℕᵒpos false = 𝟘?
ℕᵒpos true = 𝟙?

ℕᵒ : ltyp ℓ
ℕᵒ = Wᵒ 𝟚ᵒ (ℕᵒsh , ℕᵒpos)

pattern zeroᵒ f = sup false f
pattern sucᵒ f = sup true f


Finᵒ : (n : ℕᵒ {ℓ} ．) → ltyp ℓ
Finᵒ (zeroᵒ f) = 𝟘ᵒ
Finᵒ (sucᵒ f) = 𝟙ᵒ ⊕ Finᵒ (f tt*)


ℕfree : (n : ℕᵒ {ℓ} ．) → ◇ ⇒ n ∶ ℕᵒ
ℕfree (zeroᵒ f) = unitr'
ℕfree (sucᵒ f) = unitl' ∘ unitr' ∘ ℕfree (f tt*)

double' : (n : ℕᵒ {ℓ} ．) → (n ∶ ℕᵒ) ^ 0 ⊩ ℕᵒ
double' (zeroᵒ f) = zeroᵒ f , unitr'
double' (sucᵒ f) = (sucᵒ (λ _ → sucᵒ (λ _ → double' (f tt*) .fst))) ,
  unitl' ∘ (unitr' ∘ (unitl' ∘ (unitr' ∘ ℕfree (double' (f tt*) .fst))))

double : ◇ {ℓ} ⊩ (⟨ ℕᵒ ⟩^ 0 ⊸ ℕᵒ)
double = ⊸I {A = ℕᵒ} {B = λ _ → ℕᵒ}
  (λ n → Coerce {A = ℕᵒ} unitr (double' n))


-- we can compute the double of 4
test : real {A = ℕᵒ {ℓ-zero}} (double' (sucᵒ (λ _ → sucᵒ (λ _ → zeroᵒ (λ ())))))
  ≡ sucᵒ (λ _ → sucᵒ (λ _ → sucᵒ (λ _ → sucᵒ (λ _ → zeroᵒ (λ ())))))
test = refl



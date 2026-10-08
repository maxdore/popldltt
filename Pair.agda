{-# OPTIONS --safe #-}

module DLTT.Pair where

open import DLTT.Base

private
  variable
    ℓ : Level

module _ {A : ltyp ℓ}  {B : A ↦ ltyp} {Δ₀ Δ₁ : sply ℓ} {m : ℕ}  where
  compsp⊗ : (p : (⟨ x ∈ A ⟩^ m ⊗ B x) ．)
    → (p ∶ ⟨ x ∈ A ⟩^ m ⊗ B x ) ≡ (λ (x , y) → ((x ∶ A) ^ m ⨾ y ∶ B x)) p
  compsp⊗ p = refl

module _ {A : ltyp ℓ} {B : A ↦ ltyp} {m : ℕ}  {Δ₀ Δ₁ : sply ℓ}  where
  intro⊗ : ((a , _) : Δ₀ ⊩ A)
    → Δ₁ ⊩ B a
    → Δ₀ ^ m ⨾ Δ₁ ⊩ ⟨ x ∈ A ⟩^ m ⊗ B x
  intro⊗ (a , δ₀) (b , δ₁) = (a , b) , ⇒^ m δ₀ ⨾ᶠ δ₁

module _ {A : ltyp ℓ}  {B : A ↦ ltyp} {m : ℕ} {C : (Σᵒ A m B) ． → ltyp ℓ} {Δ₀ Δ₁ : sply ℓ}  where
  elim⊗ : ((p , _) : Δ₀ ⊩ ⟨ x ∈ A ⟩^ m ⊗ B x )
    → ((x : A ．) (y : B x ．) → Δ₁ ⨾ (x ∶ A) ^ m ⨾ y ∶ B x ⊩ C (x , y))
    → Δ₁ ⨾ Δ₀ ⊩ C p
  elim⊗ ((a , b) , δ) f = f a b .fst , f a b .snd ∘ id ⨾ᶠ δ

module _ {A : ltyp ℓ}  {B : A ↦ ltyp} {m : ℕ} {C : (Σᵒ A m B) ． → ltyp ℓ} {Δ₀ Δ₁ : sply ℓ}  where
  ⊗β :
      (c : (x : A ．) (y : B x ．) → Δ₁ ⨾ (x ∶ A) ^ m ⨾ y ∶ B x ⊩ C (x , y))
    → ((x : A ．) (y : B x ．) → Δ₁ ⨾ (x ∶ A) ^ m ⨾ y ∶ B x ⊩ C (x , y))
  ⊗β 𝓙 x y  = elim⊗ {A = A} {B} {m} {C} (intro⊗ {A = A} {B} (Idᵒ A x) (Idᵒ (B x) y)) 𝓙

  -- Equality of linear terms follows from equality of host terms
  ⊗Cut : (𝓙 : (x : A ．) (y : B x ．) → Δ₁ ⨾ (x ∶ A) ^ m ⨾ y ∶ B x ⊩ C (x , y))
    → (x : A ．) → (y : (B x) ．)
    → fst (⊗β 𝓙 x y) ≡ fst (𝓙 x y)
  ⊗Cut 𝓙 x y = refl

module snd {A : ltyp ℓ} {B : A ↦ ltyp}  where
  sndᵒ : (z : (⟨ x ∈ A ⟩^ 0 ⊗ B x) ．) → (z ∶ ⟨ x ∈ A ⟩^ 0 ⊗ B x) ⊩ B (fst z)
  sndᵒ z = Coerce {A = B (fst z)} unitl'
    (elim⊗ {A = A} {B} {C = λ z → B (fst z)} {z ∶ (⟨ x ∈ A ⟩^ 0 ⊗ B x)} {◇}
    (Idᵒ (⟨ x ∈ A ⟩^ 0 ⊗ B x) z) (λ x y → Coerce {A = B x} (unitl ∘ unitl) (Idᵒ (B x) y)))

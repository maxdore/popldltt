{-# OPTIONS --safe #-}

module DLTT.Function where

open import DLTT.Base

private
  variable
    ℓ ℓ' : Level



-- Elaboration of the dependent function types

module _ {Δ : sply ℓ} {A : ltyp ℓ} {B : A ↦ ltyp} {m : ℕ} where
  compsp⊸ :
    (f : (⟨ x ∈ A ⟩^ m ⊸ B x) ．)
    → (f ∶ ⟨ x ∈ A ⟩^ m ⊸ B x) ≡ Λ⟨ x ∶ A ． ⟩ [ (x ∶ A) ^ m , f x ∶ B x ]
  compsp⊸ f = refl

  ⊸I : (f : (x : A ．) → Δ ⨾ (x ∶ A) ^ m ⊩ B x)
    → Δ ⊩ ⟨ x ∈ A ⟩^ m ⊸ B x
  ⊸I f = (λ x → f x .fst) , bind (λ x → curry (f x .snd))

module _ {A : ltyp ℓ} {B : A ↦ ltyp} {Δ₀ Δ₁ : sply ℓ} {m : ℕ} where
  ⊸App :
    Δ₀ ⊩ ⟨ x ∈ A ⟩^ m ⊸ B x
    → ((a , _) : Δ₁ ⊩ A)
    → (Δ₀ ⨾ Δ₁ ^ m ⊩ B a)
  ⊸App (f , δ₀) (a , δ₁) = f a , uncurry (free δ₀ a) ∘ id ⨾ᶠ ⇒^ m δ₁


-- Elaboration of the !-functions (Section 5)

module _  {A : ltyp ℓ} {B : A ↦ ltyp} where
  ⊸!I : {Δ : sply ℓ}
    → (f : (x : A ．) → Δ ⨾ ! (x ∶ A) ⊩ B x)
    → Δ ⊩ !⟨ x ∈ A ⟩ ⊸ B x
  ⊸!I f = (λ x → f x .fst) , bind (λ x → curry (f x .snd))

  ⊸!App : {Δ₀ Δ₁ : sply ℓ} {m : ℕ}
    → Δ₀ ⊩ !⟨ x ∈ A ⟩ ⊸ B x
    → ((a , _) : Δ₁ ⊩ A)
    → (Δ₀ ⨾ ! Δ₁ ⊩ B a)
  ⊸!App (f , δ₀) (a , δ₁) = f a , uncurry (free δ₀ a) ∘ id ⨾ᶠ !ᶠ δ₁


module FunBeta {A : ltyp ℓ} {B : A ↦ ltyp} {Δ₀ Δ₁ : sply ℓ} {m : ℕ}where
  ⊸βLeft : ((x : A ．) → Δ₀ ⨾ (x ∶ A) ^ m ⊩ B x)
    → ((a , _) : Δ₁ ⊩ A)
    → (Δ₀ ⨾ Δ₁ ^ m ⊩  B a)
  ⊸βLeft b = ⊸App {A = A} {B} (⊸I {A = A} {B} (λ x → b x))

  ⊸βRight : (b : (x : A ．) → Δ₀ ⨾ (x ∶ A) ^ m ⊩ B x)
      → ((a , _) : Δ₁ ⊩ A)
    → (Δ₀ ⨾ Δ₁ ^ m ⊩  B a)
  ⊸βRight b (a , δ₁) = Cut {A = A} {B a} (a , δ₁) (b a)

   -- Equality of linear terms is defined as equality of host terms
  ⊸βLeftRight≡ :
    (𝓙₀ : (x : A ．) → Δ₀ ⨾ (x ∶ A) ^ m ⊩ B x)
    → (𝓙₁  : Δ₁ ⊩ A)
    → fst (⊸βLeft 𝓙₀ 𝓙₁) ≡ fst (⊸βRight 𝓙₀ 𝓙₁)
  ⊸βLeftRight≡ 𝓙₀ 𝓙₁ = refl

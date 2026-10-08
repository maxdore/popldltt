{-# OPTIONS --safe #-}

module DLTT.Bool where

open import DLTT.Base

private
  variable
    ℓ  : Level



-- The computation rule for boolean term supplies follows from how we
-- interpreted the linear Booleans


𝟚ᵒ◇ : (a : 𝟚 {ℓ}) → ((a ∶ 𝟚ᵒ) ≡ ◇)
𝟚ᵒ◇ a = refl

trueᵒ : (◇ ⊩ 𝟚ᵒ {ℓ})
trueᵒ = true , id

falseᵒ : (◇ ⊩ 𝟚ᵒ {ℓ})
falseᵒ = false , id

module _ {C : 𝟚ᵒ {ℓ} ↦ ltyp} {Δ Δ₀ Δ₁ : sply ℓ} {x : C true ．} {y : C false ．} where
  𝟚ᵒE : ((b , _) : Δ ⊩ 𝟚ᵒ)
    → (Δ₀ ⊩ C true)
    → (Δ₁ ⊩ C false)
    → (Δ ⨾ Δ₀ ^ ∣ b ∣ ⨾ Δ₁ ^ ∣ ¬ b ∣ ⊩ C b)
  𝟚ᵒE (true , δ) (c₀ , δ₀) (c₁ , δ₁) = c₀ , δ₀ ∘ (unitl ∘ δ ⨾ᶠ (unitr ∘ unitr))
  𝟚ᵒE (false , δ) (c₀ , δ₀) (c₁ , δ₁) = c₁ , δ₁ ∘ (unitl ∘ δ ⨾ᶠ (unitr ∘ unitl))


module Beta {C : 𝟚ᵒ {ℓ} ↦ ltyp} {Δ₀ Δ₁ : sply ℓ} where
  𝟚ᵒβtrue : (Δ₀ ⊩ C true)
    → (Δ₀ ⊩ C false)
    → Δ₀ ⊩ C true
  𝟚ᵒβtrue 𝓙₀ 𝓙₁ = Coerce {A = C true} (unitl' ∘ unitr' ∘ unitr')
    (𝟚ᵒE {C = C} {x = fst 𝓙₀} {y = fst 𝓙₁} trueᵒ 𝓙₀ 𝓙₁)

  𝟚ᵒβtrue≡ : (𝓙₀ :  Δ₀ ⊩ C true) (𝓙₁ : Δ₀ ⊩ C false)
    → fst (𝟚ᵒβtrue 𝓙₀ 𝓙₁) ≡ fst 𝓙₀
  𝟚ᵒβtrue≡ 𝓙₀ 𝓙₁ = refl

  𝟚ᵒβfalse : (Δ₀ ⊩ C true)
    → (Δ₀ ⊩ C false)
    → Δ₀ ⊩ C false
  𝟚ᵒβfalse 𝓙₀ 𝓙₁ = Coerce {A = C false} ((id ⨾ᶠ unitl') ∘ unitl' ∘ unitr')
    (𝟚ᵒE {C = C} {x = fst 𝓙₀} {y = fst 𝓙₁} falseᵒ 𝓙₀ 𝓙₁)

  𝟚ᵒβfalse≡ : (𝓙₀ :  Δ₀ ⊩ C true) (𝓙₁ : Δ₀ ⊩ C false)
    → fst (𝟚ᵒβfalse 𝓙₀ 𝓙₁) ≡ fst 𝓙₁
  𝟚ᵒβfalse≡ 𝓙₀ 𝓙₁ = refl



-- exponentiating a supply with a bool and its negation is the same as the
-- supply by itself

splitSply : {Δ : sply ℓ} (b : 𝟚 {ℓ}) → Δ ⇒ Δ ^ ∣ b ∣ ⨾ Δ ^ ∣ ¬ b ∣
splitSply true = unitr' ∘ unitr'
splitSply false = unitl' ∘ unitr'

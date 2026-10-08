{-# OPTIONS --safe #-}

module DLTT.Unit where

open import DLTT.Base

private
  variable
    ℓ  : Level


𝟙ᵒI : ◇ {ℓ} ⊩ 𝟙ᵒ
𝟙ᵒI = tt* , id


module _ {Δ₀ Δ₁ : sply ℓ} {C : 𝟙ᵒ {ℓ} ↦ ltyp} where
  𝟙ᵒE : ((t , _) : Δ₀ ⊩ 𝟙ᵒ)
    → (Δ₁ ⊩ C tt*)
    → Δ₀ ⨾ Δ₁ ⊩ C t
  𝟙ᵒE (tt* , δ₀) (c , δ₁) = c , unitl ∘ δ₀ ⨾ᶠ δ₁

{-# OPTIONS --safe #-}

module DLTT.Empty where

open import DLTT.Base

private
  variable
    ℓ  : Level


module _ {Δ : sply ℓ} {C : 𝟘ᵒ {ℓ} ↦ ltyp} where
  𝟘ᵒE : ((e , _) : Δ ⊩ 𝟘ᵒ)
    → Δ ⊩ C e
  𝟘ᵒE (() , _)

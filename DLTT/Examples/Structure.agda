{-# OPTIONS --safe #-}

module DLTT.Examples.Structure where

open import DLTT.Base

private
  variable
    ℓ ℓ' : Level

ExpSupply : {A : ltyp ℓ} {B : A ↦ ltyp} (x : A ．) → (y : (B x) ．) → sply ℓ
ExpSupply {A = A} {B} x y = x ∶ A ⨾ y ∶ B x ⨾ x ∶ A


module Coercions where

ϵ : (m : ℕ) → ◇ ^ m ⇒ ◇ {ℓ}
ϵ zero = id
ϵ (suc m) = ϵ m ∘ unitl

ϵ' : (m : ℕ) → ◇ {ℓ} ⇒ ◇ ^ m
ϵ' zero = id
ϵ' (suc m) = unitl' ∘ ϵ' m

ϕ : {Δ : sply ℓ} → (m n : ℕ) → Δ ^ (m + n) ⇒ Δ ^ m ⨾ Δ ^ n
ϕ zero n = unitl'
ϕ (suc m) n = assoc ∘ id ⨾ᶠ ϕ m n

ϕ' : {Δ : sply ℓ} → (m n : ℕ) → Δ ^ m ⨾ Δ ^ n ⇒ Δ ^ (m + n)
ϕ' zero n = unitl
ϕ' (suc m) n = id ⨾ᶠ ϕ' m n ∘ assoc'

ψ : {Δ₀ Δ₁ : sply ℓ} → (m : ℕ) → (Δ₀ ⨾ Δ₁) ^ m ⇒ Δ₀ ^ m ⨾ Δ₁ ^ m
ψ zero = unitr'
ψ (suc m) =  assoc ∘ (id ⨾ᶠ assoc' ∘ (id ⨾ᶠ (swap ⨾ᶠ id) ∘ (id ⨾ᶠ assoc ∘ (assoc' ∘ id ⨾ᶠ ψ m))))

ψ' : {Δ₀ Δ₁ : sply ℓ} → (m : ℕ) → Δ₀ ^ m ⨾ Δ₁ ^ m ⇒ (Δ₀ ⨾ Δ₁) ^ m
ψ' zero = unitl
ψ' (suc m) = id ⨾ᶠ ψ' m ∘ (assoc' ∘ ((assoc ∘ (id ⨾ᶠ swap) ∘ assoc') ⨾ᶠ id ∘ assoc))

μ : {Δ : sply ℓ} → (m n : ℕ) → Δ ^ (m * n) ⇒ (Δ ^ m) ^ n
μ zero n = ϵ' n
μ (suc m) n = ψ' n ∘ (swap ∘ (μ m n ⨾ᶠ id ∘ (swap ∘ ϕ n (m * n))))


module ExpConv where

^comm : {Δ : sply ℓ} {A : ltyp ℓ} → (m n : ℕ)
  → Δ ^ (m + n) ⊩ A
  → Δ ^ (n + m) ⊩ A
^comm {A = A} m n = Coerce {A = A} (ϕ' m n ∘ (swap ∘ ϕ n m))


module LinearRules where

Exch : {Δ₀ Δ₁ : sply ℓ} {A : ltyp ℓ}
  → Δ₀ ⨾ Δ₁ ⊩ A
  → Δ₁ ⨾ Δ₀ ⊩ A
Exch {A = A} = Coerce {A = A} swap

Varᵒ : (A : ltyp ℓ) → (x : A ．) →
  x ∶ A ⊩ A
Varᵒ A x = Idᵒ A x


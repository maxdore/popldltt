{-# OPTIONS --safe #-}

module DLTT.Examples.Solver where

open import DLTT.Base
open import DLTT.ProductionSolver
open import DLTT.Examples.Structure using (ExpSupply)

open SupplyExp

private
  variable
    ℓ : Level


-- Basic coercions of the symmetric monoidal structure

module Basic {Δ₀ Δ₁ Δ₂ Δ₃ : sply ℓ} where

  refl⇒ : Δ₀ ⇒ Δ₀
  refl⇒ = solve

  swap⇒ : Δ₀ ⨾ Δ₁ ⇒ Δ₁ ⨾ Δ₀
  swap⇒ = solve

  assoc⇒ : (Δ₀ ⨾ Δ₁) ⨾ Δ₂ ⇒ Δ₀ ⨾ (Δ₁ ⨾ Δ₂)
  assoc⇒ = solve

  unit⇒ : ◇ ⨾ (Δ₀ ⨾ ◇) ⨾ ◇ ⇒ Δ₀
  unit⇒ = solve

  unit⇐ : Δ₀ ⇒ (◇ ⨾ ◇) ⨾ Δ₀ ⨾ ◇
  unit⇐ = solve

  empty : ◇ ⨾ (◇ ⨾ ◇) ⇒ ◇ {ℓ}
  empty = solve

  reverse : Δ₀ ⨾ Δ₁ ⨾ Δ₂ ⨾ Δ₃ ⇒ ((Δ₃ ⨾ Δ₂) ⨾ Δ₁) ⨾ Δ₀
  reverse = solve

  shuffle : (Δ₀ ⨾ ◇ ⨾ Δ₁) ⨾ (Δ₂ ⨾ Δ₃) ⇒ (Δ₃ ⨾ Δ₁) ⨾ ◇ ⨾ (Δ₀ ⨾ Δ₂)
  shuffle = solve

  -- Components may occur several times
  duplicates : Δ₀ ⨾ Δ₁ ⨾ Δ₀ ⇒ Δ₀ ⨾ Δ₀ ⨾ Δ₁
  duplicates = solve

  -- Components which are not ◇ or _⨾_ are treated as atoms, so the solver also
  -- reorders the other supply formers
  atoms : ! Δ₀ ⨾ [ Δ₁ , Δ₂ ] ⇒ [ Δ₁ , Δ₂ ] ⨾ ! Δ₀
  atoms = solve


-- Goals are normalised first, so supply exponentiation with a concrete
-- exponent is unfolded

module Exponents {Δ₀ Δ₁ : sply ℓ} where

  ^unfold : Δ₀ ^ 3 ⇒ Δ₀ ⨾ Δ₀ ⨾ Δ₀
  ^unfold = solve

  ^split : Δ₀ ^ 5 ⇒ Δ₀ ^ 2 ⨾ Δ₀ ^ 3
  ^split = solve

  ^distr : (Δ₀ ⨾ Δ₁) ^ 2 ⇒ Δ₀ ^ 2 ⨾ Δ₁ ^ 2
  ^distr = solve

  ^unit : ◇ ^ 4 ⇒ ◇ {ℓ}
  ^unit = solve

  -- Exponents which are variables are not unfolded, but Δ ^ m is an atom
  ^atom : (m n : ℕ) → Δ₀ ^ m ⨾ Δ₁ ^ n ⇒ Δ₁ ^ n ⨾ Δ₀ ^ m
  ^atom m n = solve


-- Supplies of terms, compared up to definitional equality

module Terms {A : ltyp ℓ} {B : A ↦ ltyp} (x : A ．) (y : B x ．) where

  terms : x ∶ A ⨾ (y ∶ B x ⨾ ◇) ⇒ y ∶ B x ⨾ x ∶ A
  terms = solve

  -- ExpSupply x y unfolds to x ∶ A ⨾ y ∶ B x ⨾ x ∶ A
  expSupply : ExpSupply {A = A} {B} x y ⇒ (x ∶ A) ^ 2 ⨾ y ∶ B x
  expSupply = solve

  inject : {X : ityp ℓ} (a b : X) → ι a ⨾ ι b ⨾ ι a ⇒ ι b ⨾ (ι a ⨾ ι a)
  inject a b = solve


-- The solver can be used for the coercions of linear terms, where the supplies
-- are only determined by the surrounding terms

module LinearTerms {Δ₀ Δ₁ Δ₂ : sply ℓ} {A : ltyp ℓ} where

  exch : Δ₀ ⨾ Δ₁ ⨾ Δ₂ ⊩ A → (Δ₂ ⨾ ◇) ⨾ Δ₀ ⨾ Δ₁ ⊩ A
  exch t = Coerce {A = A} solve t

  ^comm : (Δ₀ ⨾ Δ₁) ^ 2 ⊩ A → Δ₁ ^ 2 ⨾ Δ₀ ^ 2 ⊩ A
  ^comm t = Coerce {A = A} solve t


-- Goals which are not just a reordering are rejected, e.g.
--
--   weaken : {Δ : sply ℓ} → Δ ⇒ ◇
--   weaken = solve
--
-- fails with "solve: the supplies Δ and ◇ do not consist of the same
-- components".

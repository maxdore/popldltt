{-# OPTIONS --safe #-}

module DLTT.Examples.Sum where

open import DLTT.Base
open import DLTT.Bool
open import DLTT.Pair
open import DLTT.Function


private
  variable
    ℓ ℓ' : Level




Case⊕ : (A B : ltyp ℓ) → 𝟚 {ℓ} → ltyp ℓ
Case⊕ A B true = A
Case⊕ A B false = B

-- Define internal choice using a dependent pair which case splits a Boolean
_⊕_ : (A B : ltyp ℓ) → ltyp ℓ
A ⊕ B = Σᵒ 𝟚ᵒ 0 (Case⊕ A B)

infixl 10 _⊕_

pattern inl x = (true , x)
pattern inr x = (false , x)


-- The constructors could be defined more easily as a pair
-- > inl⊕ (a , δ) = (inl a , unitl' ∘ δ)
-- but we give the derivation in the surface syntax for illustration

module _ {A B : ltyp ℓ} {Δ : sply ℓ}  where
  inl⊕ : Δ ⊩ A
    → Δ ⊩ A ⊕ B
  inl⊕ (a , δ) = Coerce {A = A ⊕ B} unitl' (intro⊗ {A = 𝟚ᵒ} {B = Case⊕ A B} (Idᵒ 𝟚ᵒ true) (a , δ))

module _ {A B : ltyp ℓ} {Δ : sply ℓ} {b : B ．} where
  inr⊕ : Δ ⊩ B
    → Δ ⊩ A ⊕ B
  inr⊕  (b , δ) = Coerce {A = A ⊕ B} unitl' (intro⊗ {A = 𝟚ᵒ} {B = Case⊕ A B} (Idᵒ 𝟚ᵒ false) (b , δ))


-- Note that elim⊕ can be implemented more easily with pattern matching directly
-- in the elaborated system, instead of using the surface syntax, as follows
-- > elim⊕ (inl x , δ) δ₀ δ₁ = (c x) , δ₀ {x} ∘ id ⨾ᶠ (unitl ∘ δ) ∘ swap ∘ id ⨾ᶠ unitr ∘ id ⨾ᶠ unitr
-- > elim⊕ (inr y , δ) δ₀ δ₁ =  d y , δ₁ {y} ∘ id ⨾ᶠ (unitl ∘ δ) ∘ swap ∘ id ⨾ᶠ unitr ∘ id ⨾ᶠ unitl
-- but we give the explicit derivation in the surface syntax for illustration.

module _ {A B : ltyp ℓ} {C : (A ⊕ B) ↦ ltyp} {Δ Δ₀ Δ₁ : sply ℓ} where
  elim⊕ : ((z , _) : Δ ⊩ A ⊕ B)
    → ((x : A ．) → (Δ₀ ⨾ x ∶ A ⊩ C (inl x)))
    → ((y : B ．) → (Δ₁ ⨾ y ∶ B ⊩ C (inr y)))
    → Δ ⨾ Δ₀ ^ ∣ fst z ∣ ⨾ Δ₁ ^ ∣ ¬ (fst z) ∣ ⊩ C z
  elim⊕ (z , δ) c d =
    Coerce {A = C z} ((id ⨾ᶠ unitr') ∘ swap)
      (⊸App {A = Case⊕ A B (fst z)} {B = λ w → C (fst z , w)} {m = 1}
        (Coerce {A = D (fst z)} unitl'
          (𝟚ᵒE {C = D} {x = cΠ .fst} {y = dΠ .fst} (fst z , id) cΠ dΠ))
        (snd z , unitl ∘ δ))
    where
      D : 𝟚ᵒ {ℓ} ↦ ltyp
      D b = Πᵒ (Case⊕ A B b) 1 (λ w → C (b , w))

      cΠ : Δ₀ ⊩ D true
      cΠ = ⊸I {A = A} {B = λ x → C (inl x)} {m = 1} (λ x → Coerce {A = C (inl x)} (id ⨾ᶠ unitr) (c x))

      dΠ : Δ₁ ⊩ D false
      dΠ = ⊸I {A = B} {B = λ y → C (inr y)} {m = 1} (λ y → Coerce {A = C (inr y)} (id ⨾ᶠ unitr) (d y))




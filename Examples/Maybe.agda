{-# OPTIONS --safe #-}

module DLTT.Examples.Maybe where

open import DLTT.Base
open import DLTT.Function

open import DLTT.Examples.Sum

private
  variable
    ℓ ℓ' : Level



Maybe : (A : ltyp ℓ) → ltyp ℓ
Maybe A = A ⊕ 𝟙ᵒ

pattern just x = (true , x)
pattern nothing = (false , tt*)

-- Host-level functions useful for dependent multiplicities.
module _ {A : ltyp ℓ} where
  isjust isnothing : (Maybe A) ． → 𝟚 {ℓ}
  isjust (just _) = true
  isjust nothing = false
  isnothing x = ¬ (isjust x)


-- The recursor for Maybe, implemented using the eliminator for ⊕
-- (note that it's easier to define this in the elaborated semantics instead of
-- using surface syntax eliminators, but we do this here for illustration)

foldMaybe : {A B : ltyp ℓ}  (z : (Maybe A) ．) (j : (A ⊸ B) ．) → (n : B ．) →
  z ∶ Maybe A ⨾ (j ∶ A ⊸ B) ^ ∣ isjust z ∣ ⨾ (n ∶ B) ^ ∣ isnothing z ∣ ⊩ B
foldMaybe {A = A} {B = B} z j n =
  Convsply {A = B}
    (elim⊕ {A = A} {B = 𝟙ᵒ} {C = λ _ → B} (Idᵒ (Maybe A) z)
      (λ x → Coerce {A = B} (id ⨾ᶠ unitr') (⊸App {A = A} {B = λ _ → B} (Idᵒ (A ⊸ B) j) (Idᵒ A x)))
      (λ _ → Coerce {A = B} unitr (Idᵒ B n)))
    (eqPow z j n)
  where
  -- Mediate between fst, snd dependent multiplicities from Sum and isjust, isnothing
  eqPow : (z : (Maybe A) ．) (j : (A ⊸ B) ．) (n : B ．) →
    (z ∶ Maybe A ⨾ (j ∶ A ⊸ B) ^ ∣ fst z ∣ ⨾ (n ∶ B) ^ ∣ ¬ (fst z) ∣)
      ≡ (z ∶ Maybe A ⨾ (j ∶ A ⊸ B) ^ ∣ isjust z ∣ ⨾ (n ∶ B) ^ ∣ isnothing z ∣)
  eqPow (just x) j n = refl
  eqPow nothing j n = refl



pairMaybe : {A B : ltyp ℓ} → (x : (Maybe A) ．) (y : (Maybe B) ．) →
  (x ∶ Maybe A) ^ ∣ isjust y ∣ ⨾ (y ∶ Maybe B) ^ ∣ isjust x ∣ ⊩ Maybe (A ⊗ B)
pairMaybe (just x) (just y) = (just (x , y)) , unitl' ∘ (swap ⨾ᶠ id ∘ unitr ⨾ᶠ id ∘ id ⨾ᶠ unitl ∘ id ⨾ᶠ unitr)
pairMaybe nothing (just y) = nothing , (unitl ∘ unitr ⨾ᶠ id) ⨾ᶠ id
pairMaybe (just x) nothing = nothing , id ⨾ᶠ (unitl ∘ unitr ⨾ᶠ id)
pairMaybe nothing nothing = nothing , id



-- We can take m copies of a supply annotated with a bang.
!^ : {Δ : sply ℓ} (b : 𝟚 {ℓ}) → ! Δ ⇒ Δ ^ ∣ b ∣
!^ true = unitr' ∘ use
!^ false = erase

pairMaybeBang : {A B : ltyp ℓ}
  → ◇ ⊩ !⟨ Maybe A ⟩ ⊸ !⟨ Maybe B ⟩ ⊸ Maybe (A ⊗ B)
pairMaybeBang {A = A} {B} =
  ⊸!I {A = Maybe A} {B = λ _ → !⟨ Maybe B ⟩ ⊸ Maybe (A ⊗ B)} (λ mx →
    ⊸!I {A = Maybe B} {B = λ _ → Maybe (A ⊗ B)} (λ my →
    Coerce {A = Maybe (A ⊗ B)}
      ((!^ (isjust my) ⨾ᶠ !^ (isjust mx)) ∘ (unitl ⨾ᶠ id))
      (pairMaybe mx my)))

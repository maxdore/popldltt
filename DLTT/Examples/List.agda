{-# OPTIONS --safe #-}

module DLTT.Examples.List where

open import DLTT.Base
open import DLTT.Function
open import DLTT.Examples.Structure
open import DLTT.Examples.Sum
open import DLTT.Examples.Maybe

private
  variable
    ℓ : Level


-- Function in the host theory often used in dependent multiplicities
module _ {A : ltyp ℓ} where
  length : List (A ．) → ℕ
  length [] = 0
  length (_ ∷ xs) = 1 + length xs


-- Computation of list term supplies
compspListᵒ : {Δ₀ Δ₁ : sply ℓ} {A : ltyp ℓ} (xs : (Listᵒ A) ．)
  → (xs ∶ Listᵒ A) ≡ foldr (λ x → x ∶ A ⨾_) ◇ xs
compspListᵒ xs = refl


-- Elaboration of the constructors
nil : {A : ltyp ℓ} → ◇ ⊩ Listᵒ A
nil = [] , id

cons : {Δ₀ Δ₁ : sply ℓ} {A : ltyp ℓ}
  → Δ₀ ⊩ A
  → Δ₁ ⊩ Listᵒ A
  → Δ₀ ⨾ Δ₁ ⊩ Listᵒ A
cons (x , δ₀) (xs , δ₁) = x ∷ xs , δ₀ ⨾ᶠ δ₁


module recList where

-- Elaboration of the non-dependent list recursor

module _ {Δ₀ Δ₁ : sply ℓ} {A B : ltyp ℓ} where
  foldrᵒ :
      Δ₀ ⊩ B
    → ((x : A ．) (y : B ．) → Δ₁ ⨾ y ∶ B ⨾ x ∶ A ⊩ B)
    → (xs : List (A ．))
    → Δ₀ ⨾ Δ₁ ^ length {A = A} xs ⨾ xs ∶ Listᵒ A ⊩ B
  foldrᵒ (n , δ₀) c [] = n , δ₀ ∘ (unitr ∘ id ⨾ᶠ unitl)
  foldrᵒ n c (x ∷ xs) =
    (c x (foldrᵒ n c xs .fst) .fst) , c x (foldrᵒ n c xs .fst) .snd
    ∘ (id ⨾ᶠ (foldrᵒ n c xs .snd ⨾ᶠ id))
    ∘ (id ⨾ᶠ (assoc ∘ (id ⨾ᶠ assoc)))
    ∘ (id ⨾ᶠ (id ⨾ᶠ (id ⨾ᶠ swap)))
    ∘ (assoc' ∘ (swap ⨾ᶠ id) ∘ assoc)
    ∘ (id ⨾ᶠ assoc')


-- The dependent version of the list recursor

module elimList {Δ₀ Δ₁ : sply ℓ} {A : ltyp ℓ} {B : Listᵒ A ↦ ltyp} where
  elimListᵒ :
    Δ₀ ⊩ B []
    → ((x : A ．) {xs : List (A ．)} (y : (B xs) ．) → Δ₁ ⨾ y ∶ B xs ⨾ x ∶ A ⊩ B (x ∷ xs))
    → (xs : List (A ．))
    → Δ₀ ⨾ Δ₁ ^ length {A = A} xs ⨾ xs ∶ Listᵒ A ⊩ B xs
  elimListᵒ (n , δ₀) c [] = n , δ₀ ∘ (unitr ∘ id ⨾ᶠ unitl)
  elimListᵒ n c (x ∷ xs) =
    (c x (elimListᵒ n c xs .fst) .fst) , c x (elimListᵒ n c xs .fst) .snd
    ∘ (id ⨾ᶠ (elimListᵒ n c xs .snd ⨾ᶠ id))
    ∘ (id ⨾ᶠ (assoc ∘ (id ⨾ᶠ assoc)))
    ∘ (id ⨾ᶠ (id ⨾ᶠ (id ⨾ᶠ swap)))
    ∘ (assoc' ∘ (swap ⨾ᶠ id) ∘ assoc)
    ∘ (id ⨾ᶠ assoc')


-- Implementing a map function using the surface recursor
map : {A B : ltyp ℓ} (xs : List (A ．)) (f : (A ⊸ B) ．) →
  (xs ∶ Listᵒ A) ⨾ (f ∶ (A ⊸ B)) ^ length {A = A} xs ⊩ Listᵒ B
map {A = A} {B} xs f = Coerce {A = Listᵒ B}
  (id ⨾ᶠ swap ∘ unitl')
  (foldrᵒ {_} {◇} {f ∶ A ⊸ B} {A} {Listᵒ B}
    (nil {A = B})
    (λ x y → Coerce {A = Listᵒ B}
      (assoc ∘ (id ⨾ᶠ ((unitr' ⨾ᶠ id) ∘ swap)))
      (cons {A = B} (⊸App {A = A} {B = λ _ → B} (Idᵒ (A ⊸ B) f) (Idᵒ A x)) (Idᵒ (Listᵒ B) y)))
    xs)




module FractionElaboration where

-- Below we give the elaboration of an eliminator for fractional lists

module ind where
-- Turning a function which assigns multiplicities to all list elements
-- separately into a fractional multiplicity
toFrac : {A : ltyp ℓ} → (A ． → ℕ) → (xs : List (A ．)) → ListFraction A xs
toFrac m = elimList tt* (λ x → m x ,_)

module _ {A B : ltyp ℓ} {m : A ． → ℕ}
  where
  recListF :
    ◇ ⊩ B
    → ((x : A ．) (y : B ．) → (x ∶ A) ^ m x ⨾ y ∶ B ⊩ B)
    → (xs : List (A ．))
    → (xs ∶ (Listᵒ A / toFrac {A = A} m)) ⊩ B
  recListF (n , δ₀) c [] = n , δ₀
  recListF n c (x ∷ xs) = c x  (recListF n c xs .fst) .fst ,
    c x (recListF n c xs .fst) .snd ∘ id ⨾ᶠ (recListF n c xs .snd)



-- More general version which is natural to use in the dependent eliminator for
-- fractional lists, where each multiplicity can also take into account the tail

toFrac' : {A : ltyp ℓ} → (A ． → (xs : List (A ．)) → ℕ) → (xs : List (A ．)) → ListFraction A xs
toFrac' m = elimList tt* (λ x {xs} ms → m x xs , ms)

module _
  {A : ltyp ℓ} {B : Listᵒ A ↦ ltyp}
  {m : A ． → (xs : List (A ．)) → ℕ}
  where
  elimListF :
    ◇ ⊩ B []
    → ((x : A ．) {xs : List (A ．)} (y : B xs ．) → (x ∶ A) ^ m x xs ⨾ y ∶ B xs ⊩ B (x ∷ xs))
    → (xs : List (A ．))
    → (xs ∶ (Listᵒ A / toFrac' {A = A} m)) ⊩ B xs
  elimListF (n , δ₀) c [] = n , δ₀
  elimListF n c (x ∷ xs) = c x  (elimListF n c xs .fst) .fst ,
    c x (elimListF n c xs .fst) .snd ∘ id ⨾ᶠ (elimListF n c xs .snd)




-- Filtering a list with a given predicate, using the surface syntax foldr

filter : {A : ltyp ℓ} {Ainh : A ． } → (p : A ． → 𝟚 {ℓ}) (xs : List (A ．))
  → (p ∶ ⟨ x ∈ A ⟩^ 0 ⊸ 𝟚ᵒ) ⨾ xs ∶ Listᵒ A / toFrac {A = A} (λ x → ∣ p x ∣) ⊩ Listᵒ A
filter {A = A} {Ainh} p xs =
  Coerce {A = Listᵒ A} (unitl ∘ (uncurry id ∘ unitr' ∘ projFiber Ainh) ⨾ᶠ id)
  ((recListF {_} {A} {Listᵒ A} {λ x → ∣ p x ∣}
  (nil {A = A})
  λ x zs → (if p x then x ∷ zs else zs) , c x zs) xs)
  where
  -- (p ∶ ⟨x∈A⟩^0⊸𝟚ᵒ) is definitionally Λ⟨x∶A．⟩ [ ◇ , ◇ ], since p is used
  -- 0 times and (_∶𝟚ᵒ) is always ◇. To discard this unused resource we
  -- project out a single fiber (needs an assumed inhabitant Ainh, as A
  -- could be empty) and evaluate the resulting trivial [◇,◇] hom.
  projFiber : (x : A ．) → Λ (A ．) (λ x → [ ◇ , ◇ ]) ⇒ [ ◇ , ◇ ]
  projFiber = free (id {Δ = Λ (A ．) (λ x → [ ◇ , ◇ ])})

  c : (x : A ．) (zs : List (A ．))
    → (x ∶ A) ^ ∣ p x ∣ ⨾ zs ∶ Listᵒ A ⇒ if p x then x ∷ zs else zs ∶ Listᵒ A
  c x zs with p x
  ... | false = unitl
  ... | true = unitr ⨾ᶠ id

-- Internalising filter as a function in the empty context
filterF : {A : ltyp ℓ} {Ainh : A ． }
  → ◇ ⊩ ⟨ p ∈ (⟨ x ∈ A ⟩^ 0 ⊸ 𝟚ᵒ) ⟩^ 1 ⊸ ( (Listᵒ A / toFrac {A = A} (λ x → ∣ p x ∣)) ⊸ Listᵒ A )
filterF {A = A} {Ainh} = ⊸I
  {A = ⟨ x ∈ A ⟩^ 0 ⊸ 𝟚ᵒ}
  {B = λ p → (Listᵒ A / toFrac {A = A} (λ x → ∣ p x ∣)) ⊸ Listᵒ A}
  {m = 1}
  (λ p → Coerce {A = (Listᵒ A / toFrac {A = A} (λ x → ∣ p x ∣)) ⊸ Listᵒ A} (unitr ∘ unitl)
    (⊸I {A = Listᵒ A / toFrac {A = A} (λ x → ∣ p x ∣)} {B = λ _ → Listᵒ A} {m = 1}
      (λ xs → Coerce {A = Listᵒ A} (id ⨾ᶠ unitr) (filter {A = A} {Ainh} p xs))))


-- Extracting the head of a list with a fractional multiplicity.
-- Note that we define this directly in the elaborated semantics.

head  : {A : ltyp ℓ} (xs : List (A ．)) →
  xs ∶ Listᵒ A / elimList tt* (λ x {xs} _ → 1 , constL A xs 0) ⊩ Maybe A
head [] = nothing , unitr'
head {A = A} (x ∷ xs) = just x , swap ∘ unitr ⨾ᶠ constL0 A xs

-- Packaging up as a function
headF : {A : ltyp ℓ} →
  ◇ ⊩ (Listᵒ A / elimList tt* (λ x {xs} _ → 1 , constL A xs 0)) ⊸ Maybe A
headF {A = A} = ⊸I
  {A = Listᵒ A / elimList tt* (λ x {xs} _ → 1 , constL A xs 0)}
  {B = λ _ → Maybe A}
  (λ xs → Coerce {A = Maybe A} (unitr ∘ unitl) (head xs))



module ListFunctions (A : ltyp ℓ) where
  infixr 5 _++_

  _++_ : {Δ₀ Δ₁ : sply ℓ}
    → Δ₀ ⊩ Listᵒ A
    → Δ₁ ⊩ Listᵒ A
    → Δ₀ ⨾ Δ₁ ⊩ Listᵒ A
  _++_ (xs , δ₀) ys = Coerce {A = Listᵒ A}
    (id ⨾ᶠ (ϵ' (length {A = A} xs) ⨾ᶠ δ₀) ∘ id ⨾ᶠ unitl' ∘ swap)
    (foldrᵒ {_} {_} {◇} {A} {Listᵒ A}
      ys
      (λ x y → Coerce {A = Listᵒ A} (swap ∘ unitl) (cons {A = A} (Idᵒ A x) (Idᵒ (Listᵒ A) y)))
      xs)



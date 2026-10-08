{-# OPTIONS --safe #-}

module DLTT.Examples.Quicksort where

open import DLTT.Base
open import DLTT.Function
open import DLTT.Bool
open import DLTT.Examples.Structure
open import DLTT.Examples.List

private
  variable
    ℓ : Level


module _ {A : ltyp ℓ} where
  open ListFunctions A

  -- Variant of filter where the predicate lives in the host theory only, so no
  -- linear resource for it needs to be discarded
  filterSimple : (p : A ． → 𝟚 {ℓ}) (xs : List (A ．))
    → xs ∶ Listᵒ A / toFrac {A = A} (λ x → ∣ p x ∣) ⊩ Listᵒ A
  filterSimple p = recListF {A = A} {Listᵒ A} {λ x → ∣ p x ∣}
    (nil {A = A})
    (λ x zs → (if p x then x ∷ zs else zs) , c x zs)
    where
    c : (x : A ．) (zs : List (A ．))
      → (x ∶ A) ^ ∣ p x ∣ ⨾ zs ∶ Listᵒ A ⇒ if p x then x ∷ zs else zs ∶ Listᵒ A
    c x zs with p x
    ... | false = unitl
    ... | true = unitr ⨾ᶠ id

  -- A linear supply for a list can be split into two fractional supplies
  -- according to a predicate and its negation, since each element is then
  -- used exactly once
  splitList : (p : A ． → 𝟚 {ℓ}) (xs : List (A ．))
    → xs ∶ Listᵒ A
      ⇒ (xs ∶ Listᵒ A / toFrac {A = A} (λ y → ∣ p y ∣)) ⨾ (xs ∶ Listᵒ A / toFrac {A = A} (λ y → ∣ ¬ p y ∣))
  splitList p [] = unitr'
  splitList p (x ∷ xs) =
    assoc ∘ id ⨾ᶠ (assoc' ∘ swap ⨾ᶠ id ∘ assoc) ∘ assoc'
    ∘ splitSply (p x) ⨾ᶠ splitList p xs

  -- Quicksort recursing on the two partitions of the tail.

  -- This is the naive functional program, just slightly complicated since we
  -- have to convince Agda's type checker that our function terminates: since
  -- the tail is used twice (filtered into each side), the program is not
  -- obviously structurally recursive. We hence use as a measure the length of
  -- the list and recurse on this

  -- Filtering does not increase the length of a list
  ifLength : (b : 𝟚 {ℓ}) (x : A ．) (zs : List (A ．)) {n : ℕ}
    → length {A = A} zs ≤ n → length {A = A} (if b then x ∷ zs else zs) ≤ suc n
  ifLength true x zs l = s≤s l
  ifLength false x zs l = ≤suc l

  filterLength : (p : A ． → 𝟚 {ℓ}) (xs : List (A ．)) {n : ℕ}
    → length {A = A} xs ≤ n → length {A = A} (filterSimple p xs .fst) ≤ n
  filterLength p [] l = l
  filterLength p (x ∷ xs) (s≤s l) = ifLength (p x) x (filterSimple p xs .fst) (filterLength p xs l)


  module _ {_<_ : A ． → A ． → 𝟚 {ℓ}} where

    -- The elements smaller than the pivot go to the left, all others to the
    -- right, and both partitions are sorted recursively
    quicksortBounded : (n : ℕ) (xs : List (A ．)) → length {A = A} xs ≤ n
      → xs ∶ Listᵒ A ⊩ Listᵒ A
    quicksortBounded n [] _ = nil {A = A}
    quicksortBounded zero (x ∷ xs) ()
    quicksortBounded (suc n) (x ∷ xs) (s≤s l) = Coerce {A = Listᵒ A}
      (id ⨾ᶠ (unitr' ⨾ᶠ id) ∘ assoc' ∘ swap ⨾ᶠ id ∘ assoc ∘ id ⨾ᶠ splitList (λ y → y < x) xs)
      (sortPart (_< x) ++ Idᵒ (Listᵒ A) (x ∷ []) ++ sortPart (λ y → ¬ (y < x)))
      where
      -- Sorting a partition: the fractional supply of xs is turned into a
      -- linear supply of the filtered list, which is then sorted recursively
      sortPart : (p : A ． → 𝟚 {ℓ})
        → xs ∶ Listᵒ A / toFrac {A = A} (λ y → ∣ p y ∣) ⊩ Listᵒ A
      sortPart p = Coerce {A = Listᵒ A} (filterSimple p xs .snd)
        (quicksortBounded n (filterSimple p xs .fst) (filterLength p xs l))

    quicksort : (xs : List (A ．)) →
      xs ∶ Listᵒ A ⊩ Listᵒ A
    quicksort xs = quicksortBounded (length {A = A} xs) xs (≤refl _)

    -- Internalising quicksort as a function
    quicksortF : ◇ ⊩ Listᵒ A ⊸ Listᵒ A
    quicksortF = ⊸I {A = Listᵒ A} {B = λ _ → Listᵒ A}
      (λ xs → Coerce {A = Listᵒ A} (unitr ∘ unitl) (quicksort xs))


  -- Quick test sorting 10 numbers
private
  test : real {A = Listᵒ (Ground ℕ)}
          (quicksort {A = Ground ℕ} {ltℕ} (5 ∷ 3 ∷ 8 ∷ 1 ∷ 9 ∷ 2 ∷ 7 ∷ 3 ∷ 0 ∷ 6 ∷ []))
    ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  test = refl



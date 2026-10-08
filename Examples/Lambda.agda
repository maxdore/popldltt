{-# OPTIONS --safe #-}

module DLTT.Examples.Lambda where

open import DLTT.Base
open import DLTT.Function
open import DLTT.Examples.Sum
open import DLTT.Examples.Structure


module _ {ℓ : Level} {𝕧 : ltyp ℓ} {_≡?_ : 𝕧 ． → 𝕧 ． → 𝟚 {ℓ}} where


  -- Defining the Lambda data type using a W-type
  -- The first case is the variable case with no recursive fields;
  -- the second the application of two terms;
  -- and the third the abstraction case over a single term.
  CaseΛ : depfinltyp (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧)
  CaseΛ =  (switchᵒ , switchᵒsnd) where
    switchᵒ : ((𝕧 ⊕ 𝟙ᵒ) ⊕ 𝕧) ． → ltyp ℓ
    switchᵒ (inl (inl x)) = 𝟘ᵒ
    switchᵒ (inl (inr tt*)) = 𝟚ᵒ
    switchᵒ (inr x) = 𝟙ᵒ
    switchᵒsnd : (x : (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) ．) → List (switchᵒ x ．)
    switchᵒsnd (inl (inl _)) = 𝟘?
    switchᵒsnd (inl (inr tt*)) = 𝟚?
    switchᵒsnd (inr x) = 𝟙?

  Lambda : ltyp ℓ
  Lambda = Wᵒ (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) CaseΛ

  pattern var x f = sup (inl (inl x)) f
  pattern app f  = sup (inl (inr tt*)) f
  pattern lam x f  = sup (inr x) f

  freeocc : Lambda ． → 𝕧 ． → ℕ
  freeocc (var y f) x = ∣ y ≡? x ∣
  freeocc (app f) r = freeocc (f true) r + freeocc (f false) r
  freeocc (lam y f) x with y ≡? x
  ... | false = freeocc (f tt*) x
  ... | true = 0


  -- The fractional multiplicity assigning 1 to all nodes of the tree
  -- except of free occurrences of the given variable

  except : 𝕧 ． → (s : Lambda ．) → Fraction (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) CaseΛ s
  except x (var y f) = ∣ ¬ (y ≡? x) ∣ , λ ()
  except x (app f) = 1 , λ r → except x (f r)
  except x (lam y f) with y ≡? x
  ...| false = 1 , λ r → except x (f r)
  ...| true = 1 , λ r → const (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) CaseΛ (f r) 1


  -- We implement the substitution function by pattern matching on the given
  -- Lambda term.

  substC : (s : Lambda ．) (x : 𝕧 ．) (t : Lambda ．)
    → (s ∶ (Wᵒ (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) & CaseΛ / (except x))) ⨾ (t ∶ Lambda) ^ freeocc s x ⊩ Lambda
  substC (var y f) x t with y ≡? x
  ...| false = (var y f) , unitr ∘ unitr
  ...| true = t , unitl ∘ unitl ⨾ᶠ unitr
  substC (app f) x t =
    (app λ r → substC (f r) x t .fst) ,
    (unitr {Δ = ◇ ⨾ ◇ ⨾ ◇} ⨾ᶠ (substC (f false) x t .snd ⨾ᶠ (unitr' ∘ substC (f true) x t .snd)))
    ∘ ((id ⨾ᶠ assoc)
        ∘ (id ⨾ᶠ (id ⨾ᶠ (assoc' ∘ (swap ⨾ᶠ id) ∘ assoc)))
        ∘ (id ⨾ᶠ assoc')
        ∘ assoc'
        ∘ (id ⨾ᶠ (swap ∘ ϕ (freeocc (f true) x) (freeocc (f false) x))))
    ∘ ((id ⨾ᶠ id ⨾ᶠ unitr) ⨾ᶠ id)
  substC (lam y f) x t with y ≡? x
  ... | false = (lam y (λ r → substC (f r) x t .fst)) ,
    (id ⨾ᶠ swap) ∘ assoc' ∘ (id ⨾ᶠ (substC (f tt*) x t .snd))
    ∘ (id ⨾ᶠ (id ⨾ᶠ unitl)) ∘ (id ⨾ᶠ assoc') ∘ assoc'
  ... | true = (lam y f) , const1 (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) CaseΛ (lam y f) ∘ (id ⨾ᶠ unitr' ∘ ((id ⨾ᶠ unitr) ∘ unitr))


  -- Turning the program into a function in the empty context and supply

  subst : ◇ ⊩ ⟨ x ∈ 𝕧 ⟩^ 0 ⊸ (⟨ s ∈ (Wᵒ (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) & CaseΛ / (except x)) ⟩^ 1 ⊸ (⟨ Lambda ⟩^ freeocc s x ⊸ Lambda))
  subst = ⊸I {A = 𝕧} {B = λ x → ⟨ s ∈ (Wᵒ (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) & CaseΛ / (except x)) ⟩^ 1 ⊸ (⟨ Lambda ⟩^ freeocc s x ⊸ Lambda)}
    (λ x → Coerce {A = ⟨ s ∈ (Wᵒ (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) & CaseΛ / (except x)) ⟩^ 1 ⊸ (⟨ Lambda ⟩^ freeocc s x ⊸ Lambda)} unitr
      (⊸I {A = Wᵒ (𝕧 ⊕ 𝟙ᵒ ⊕ 𝕧) & CaseΛ / (except x)} {B = λ s → ⟨ Lambda ⟩^ freeocc s x ⊸ Lambda}
        (λ s → Coerce {A = ⟨ Lambda ⟩^ freeocc s x ⊸ Lambda} (unitr ∘ unitl)
          (⊸I {A = Lambda} {B = λ _ → Lambda}
            (λ t → substC s x t)))))

{-# OPTIONS --safe #-}

module DLTT.W where

open import DLTT.Base
open import DLTT.Examples.Sum

private
  variable
    ℓ ℓ' : Level



module _
  {A : ltyp ℓ} {B : A ↦ finltyp}
  where
  compspWᵒ : (p : (Wᵒ A B) ．)
    → (p ∶ Wᵒ A B) ≡ elimW (λ x f Δ → x ∶ A ⨾ ⨂ (B .fst x) (B .snd x) Δ) p
  compspWᵒ f = refl


module _
  {A : ltyp ℓ} {(B , bs) : A ↦ finltyp}
  {Δ₀ : sply ℓ}
  {Δ₁ : {x : A ．} → B x ． → sply ℓ}
  where
  introWᵒ :
    ((a , _) : Δ₀ ⊩ A)
    → (f : (y : B a ．) → Δ₁ y ⊩ Wᵒ A (B , bs))
    → Δ₀ ⨾ ⨂ (B a) (bs a) Δ₁ ⊩ Wᵒ A (B , bs)
  introWᵒ (a , δ₀) f = sup a (λ x → f x .fst) , δ₀ ⨾ᶠ ⨂ᶠ (λ x → f x .snd)

module _
  {A : ltyp ℓ} {(B , bs) : A ↦ finltyp}
  {C : Wᵒ A (B , bs) ↦ ltyp}
  {Δ₁ : A ． → sply ℓ}
  where
  elimWᵒ' :
    (c : (x : A ．) (f : B x ． → Wᵒ A (B , bs) ．) (g : (y : B x ．) → C (f y) ．) →
      (x ∶ A)  ⨾ Δ₁ x ⨾ ⨂ (B x) (bs x) (λ y → g y ∶ C (f y)) ⊩ C (sup x f))
    → (w : Wᵒ A (B , bs) ．)
    → w ∶ Wᵒ A (B , bs) ⨾ recW (λ a Δ' → Δ₁ a ⨾ ⨂ (B a) (bs a) Δ') w ⊩ C w
  elimWᵒ' c = elimW λ a f g → c a f (λ y → g y .fst) .fst , c a f (λ y → g y .fst) .snd
    ∘ (id ⨾ᶠ (id ⨾ᶠ (⨂ᶠ (λ x → g x .snd) ∘ ⨂lax) ∘ assoc' ∘ swap ⨾ᶠ id ∘ assoc) ∘ assoc')

  elimWᵒ :
    {Δ₀ : sply ℓ}
    (c : (x : A ．) (f : B x ． → Wᵒ A (B , bs) ．) (g : (y : B x ．) → C (f y) ．) →
      (x ∶ A)  ⨾ Δ₁ x ⨾ ⨂ (B x) (bs x) (λ y → g y ∶ C (f y)) ⊩ C (sup x f))
    → ((p , _) : Δ₀ ⊩  Wᵒ A (B , bs))
    → Δ₀ ⨾ recW (λ a Δ' → Δ₁ a ⨾ ⨂ (B a) (bs a) Δ') p ⊩ C p
  elimWᵒ c (p , δ) = Coerce {A = C p} (δ ⨾ᶠ id) (elimWᵒ' c p )


module _
  {A : ltyp ℓ} {(B , bs) : A ↦ finltyp}
  {C : Wᵒ A (B , bs) ↦ ltyp}
  {Δ₀ : sply ℓ}
  {Δ₁ : A ． → sply ℓ}
  {f : {x : A ．} → (y : B x ．) → (Wᵒ A (B , bs)) ．}
  where
  compWᵒLeft :
    (c : (x : A ．) (f : B x ． → Wᵒ A (B , bs) ．) (g : (y : B x ．) → C (f y) ．) →
      (x ∶ A) ⨾ Δ₁ x ⨾ ⨂ (B x) (bs x) (λ y → g y ∶ C (f y)) ⊩ C (sup x f))
      → ((a , _) : Δ₀ ⊩ A)
      → (f : (y : B a ．) → (y ∶ B a) ⊩ Wᵒ A (B , bs))
      → Δ₀ ⨾ Δ₁ a ⨾ ⨂ (B a) (bs a) (λ y → elimWᵒ {A = A} {C = C} c (f y) .fst ∶ C (f y .fst)) ⊩
          C (sup a (λ b → f b .fst))
  compWᵒLeft c (a , δa) f = Coerce {A = C (sup a (λ b → f b .fst))} (δa ⨾ᶠ id)
    (c a (λ b → f b .fst) (λ y → elimWᵒ {A = A} {C = C} c (f y) .fst))

  compWᵒRight :
    (c : (x : A ．) (f : B x ． → Wᵒ A (B , bs) ．) (g : (y : B x ．) → C (f y) ．) →
    (x ∶ A) ⨾ Δ₁ x ⨾ ⨂ (B x) (bs x) (λ y → g y ∶ C (f y)) ⊩ C (sup x f))
    → ((a , _) : Δ₀ ⊩ A)
    → (f : (y : B a ．) → (y ∶ B a) ⊩ Wᵒ A (B , bs))
    → Δ₀ ⨾ ⨂ (B a) (bs a) (λ y → y ∶ B a) ⨾ Δ₁ a ⨾
        ⨂ (B a) (bs a) (λ y → recW (λ a' Δ' → Δ₁ a' ⨾ ⨂ (B a') (bs a') Δ') (f y .fst)) ⊩
    C (sup a (λ b → f b .fst))
  compWᵒRight c (a , δa) f = Coerce {A = C (sup a (λ b → f b .fst))}
    ((introWᵒ {A = A} {(B , bs)} {Δ₁ = λ {x} y → y ∶ B x} (a , δa) f .snd ⨾ᶠ id) ∘ assoc)
    ((elimWᵒ {A = A} {C = C} c (Idᵒ (Wᵒ A (B , bs)) (sup a (λ b → f b .fst)))))



  compWᵒRight' :
    (c : (x : A ．) (f : B x ． → Wᵒ A (B , bs) ．) (g : (y : B x ．) → C (f y) ．) →
    (x ∶ A) ⨾ Δ₁ x ⨾ ⨂ (B x) (bs x) (λ y → g y ∶ C (f y)) ⊩ C (sup x f))
    → ((a , _) : Δ₀ ⊩ A)
    → (sup a (λ b → f b)) ∶ Wᵒ A (B , bs) ⨾ recW (λ a₁ Δ' → Δ₁ a₁ ⨾ ⨂ (B a₁) (bs a₁) Δ') (sup a (λ b → f b))
      ⊩ C (sup a (λ b → f b))
  compWᵒRight' c (a , δa) = elimWᵒ {A = A} {C = C} c (Idᵒ (Wᵒ A (B , bs)) (sup a (λ b → f b)))

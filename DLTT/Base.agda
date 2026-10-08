{-# OPTIONS --safe #-}

module DLTT.Base where

open import DLTT.Prelude public


-- The type of supplies encodes objects of an SMCC

data sply (ℓ : Level) : ityp (ℓ-suc ℓ) where
  ◇ : sply ℓ
  ι : {A : ityp ℓ} (a : A) → sply ℓ
  _⨾_ : sply ℓ → sply ℓ → sply ℓ
  [_,_] : sply ℓ → sply ℓ → sply ℓ
  Λ : (A : ityp ℓ) → (Δ : A → sply ℓ) → sply ℓ
  ! : sply ℓ → sply ℓ

infixr -12 _⨾_
infixr 30 [_,_]


infixl -100 _⇒_
infixr 11 _⨾ᶠ_
infixl 10 _∘_


-- The type of productions encodes the morphisms of an SMCC, endowed with a
-- right adjoint to context extension and a linear exponential comonad

data _⇒_ {ℓ : Level} : sply ℓ → sply ℓ → ityp (ℓ-suc ℓ) where
  id : ∀ {Δ} → Δ ⇒ Δ
  _∘_ : ∀ {Δ₀ Δ₁ Δ₂} → Δ₁ ⇒ Δ₂ → Δ₀ ⇒ Δ₁ → Δ₀ ⇒ Δ₂
  _⨾ᶠ_ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} → Δ₀ ⇒ Δ₁ → Δ₂ ⇒ Δ₃ → Δ₀ ⨾ Δ₂ ⇒ Δ₁ ⨾ Δ₃

  swap : ∀ {Δ₀ Δ₁} → Δ₀ ⨾ Δ₁ ⇒ Δ₁ ⨾ Δ₀
  unitr : ∀ {Δ} → Δ ⨾ ◇ ⇒ Δ
  unitr' : ∀ {Δ} → Δ ⇒ Δ ⨾ ◇
  assoc : ∀ {Δ₀ Δ₁ Δ₂} → Δ₀ ⨾ (Δ₁ ⨾ Δ₂) ⇒ (Δ₀ ⨾ Δ₁) ⨾ Δ₂

  curry : ∀ {Δ₀ Δ₁ Δ₂} →  (Δ₀ ⨾ Δ₁) ⇒ Δ₂ → Δ₀ ⇒ [ Δ₁ , Δ₂ ]
  uncurry : ∀ {Δ₀ Δ₁ Δ₂} → Δ₀ ⇒ [ Δ₁ , Δ₂ ] →  (Δ₀ ⨾ Δ₁) ⇒  Δ₂

  bind : {Δ : sply ℓ} {(A , Θ) : Σ⟨ A ∶ ityp ℓ ⟩ (A → sply ℓ)}
    → ((x : A) → Δ ⇒ Θ x) → (Δ ⇒ Λ A Θ)
  free : {Δ : sply ℓ}  {(A , Θ) : Σ⟨ A ∶ ityp ℓ ⟩ (A → sply ℓ)}
    → (Δ ⇒ Λ A Θ) → ((x : A) → Δ ⇒ Θ x)

  !ᶠ : ∀ {Δ₀ Δ₁} → Δ₀ ⇒ Δ₁ → ! Δ₀ ⇒ ! Δ₁
  dupl : ∀ {Δ} → ! Δ ⇒ ! (Δ ⨾ Δ)
  erase : ∀ {Δ} → ! Δ ⇒ ◇

  use : ∀ {Δ} → ! Δ ⇒ Δ
  mult : ∀ {Δ} → ! Δ ⇒ ! (! Δ)
  coh◇ : ◇ ⇒ ! ◇
  coh⨾ : ∀ {Δ₀ Δ₁} → ! Δ₀ ⨾ ! Δ₁ ⇒ ! (Δ₀ ⨾ Δ₁)
  coh⨾' : ∀ {Δ₀ Δ₁} → ! (Δ₀ ⨾ Δ₁) ⇒ ! Δ₀ ⨾ ! Δ₁

infixl 25 Λ
syntax Λ A (λ x → Δ) = Λ⟨ x ∶ A ⟩ Δ



private
  variable
    ℓ ℓ' : Level

-- We can derive some productions in the presence of symmetry which are usually
-- given as data for a monoidal category

unitl : ∀ {Δ : sply ℓ} → ◇ ⨾ Δ ⇒ Δ
unitl = unitr ∘ swap

unitl' : ∀ {Δ : sply ℓ} → Δ ⇒ ◇ ⨾ Δ
unitl' = swap ∘ unitr'

assoc' : ∀ {Δ₀ Δ₁ Δ₂ : sply ℓ} → (Δ₀ ⨾ Δ₁) ⨾ Δ₂ ⇒ Δ₀ ⨾ (Δ₁ ⨾ Δ₂)
assoc' = swap
  ∘ assoc
  ∘ id ⨾ᶠ swap
  ∘ swap
  ∘ swap ⨾ᶠ id
  ∘ assoc
  ∘ swap



module SupplyExp where

-- Taking m copies of a supply and production for arbitrary terms of the natural
-- numbers allows us to derive quantitative features for our type theory

_^_ : sply ℓ → ℕ → sply ℓ
Δ ^ zero = ◇
Δ ^ (suc m) = Δ ⨾ (Δ ^ m)

infixr 50 _^_

⇒^ : ∀{ℓ}{Δ₀ Δ₁ : sply ℓ} → (m : ℕ) → Δ₀ ⇒ Δ₁ → (Δ₀ ^ m) ⇒ (Δ₁ ^ m)
⇒^ zero δ = id
⇒^ (suc m) δ = δ ⨾ᶠ ⇒^ m δ

-- The type of linear types is introduced mutually recursively with its
-- interpretation

data ltyp (ℓ : Level) : ityp (ℓ-suc ℓ)
⟦_⟧ : ltyp ℓ → Σ⟨ A ∶ ityp ℓ ⟩ (A → sply ℓ)

_． : ltyp ℓ → ityp ℓ
A ． = ⟦ A ⟧ .fst

infix -4 _．

tmsply : (A : ltyp ℓ) → A ． → sply ℓ
tmsply A x = ⟦ A ⟧ .snd x
infix -10 tmsply
syntax tmsply A x = x ∶ A


depltyp : {ℓ : Level} → ltyp ℓ → ityp (ℓ-suc ℓ)
depltyp {ℓ} A = A ． → ltyp ℓ

syntax depltyp A = A ↦ ltyp

depfinltyp : {ℓ : Level} → ltyp ℓ → ityp (ℓ-suc ℓ)
depfinltyp {ℓ} A = Σ⟨ B ∶ (A ． → ltyp ℓ) ⟩ ((x : A ．) → List (B x ．))

syntax depfinltyp A = A ↦ finltyp


module FinJoin where

⨂ : (A : ltyp ℓ) → (List (A ．)) → (Δ : A ． → sply ℓ) → sply ℓ
⨂ A [] Δ = ◇
⨂ A (a ∷ as) Δ = Δ a ⨾ ⨂ A as Δ

⨂ᶠ : {A : ltyp ℓ} {as : List (A ．)} {Δ₀ Δ₁ : A ． → sply ℓ}
  → ((x : A ．) → Δ₀ x ⇒ Δ₁ x)
  → ⨂ A as Δ₀ ⇒ ⨂ A as Δ₁
⨂ᶠ {as = []} f = id
⨂ᶠ {as = a ∷ as} f = f a ⨾ᶠ ⨂ᶠ {as = as} f

⨂lax : {A : ltyp ℓ} {as : List (A ．)} {Δ₀ Δ₁ : A ． → sply ℓ}
  → ⨂ A as Δ₀ ⨾ ⨂ A as Δ₁ ⇒ ⨂ A as (λ x → Δ₀ x ⨾ Δ₁ x)
⨂lax {as = []} = unitl
⨂lax {as = a ∷ as} = id ⨾ᶠ ⨂lax {as = as} ∘ assoc ∘ id ⨾ᶠ assoc' ∘ id ⨾ᶠ (swap ⨾ᶠ id) ∘ id ⨾ᶠ assoc ∘ assoc'



-- Needed because we need the type underlying a linear W before introducing linear types
W． :  (A : ltyp ℓ) (B : A ↦ finltyp) → ityp ℓ
W． A B = W (A ．) (λ x → B .fst x ．)

module _ (A : ltyp ℓ) (B : A ↦ finltyp) where
  Fraction : W． A B → ityp ℓ
  Fraction = recW (λ a g → ℕ × ((y : B .fst a ．) → g y))

  FractionSply : (x : W． A B) → Fraction x → sply ℓ
  FractionSply = elimW λ x f Δ (m , ms) → (x ∶ A) ^ m ⨾ ⨂ (B .fst x) (B .snd x) λ y → Δ y (ms y)

  const : (x : W． A B) → ℕ → Fraction x
  const (sup a f) m = m , (λ y → const (f y) m)


module ListFraction where

-- Definitions for fractional lists

module _ (A : ltyp ℓ) where
  ListFraction : List (A ．) → ityp ℓ
  ListFraction = foldr (λ _ → ℕ ×_) 𝟙

  Listsply : (xs : List (A ．)) → ListFraction xs → sply ℓ
  Listsply = elimList (λ x → ◇) (λ x Δ (m , ms) → (x ∶ A) ^ m ⨾ Δ ms)

  constL : (xs : List (A ．)) → ℕ → ListFraction xs
  constL [] m = tt*
  constL (x ∷ xs) m = m , (constL xs m)

  constL0 : (xs : List (A ．)) → Listsply xs (constL xs 0) ⇒ ◇
  constL0 [] = id
  constL0 (x ∷ xs) = constL0 xs ∘ unitl



module ltypsemantics where

-- A host type gathers all the linear types formers. We then define the
-- interpretation of linear types recursively, with the ground types as the base
-- case

data ltyp ℓ where
  Ground : (A : ityp ℓ) → ltyp ℓ
  𝟘ᵒ : ltyp ℓ
  𝟙ᵒ : ltyp ℓ
  𝟚ᵒ : ltyp ℓ
  Πᵒ : (A : ltyp ℓ) → ℕ → (A ↦ ltyp) → ltyp ℓ
  Π! : (A : ltyp ℓ) → (A ↦ ltyp) → ltyp ℓ
  Σᵒ : (A : ltyp ℓ) → ℕ → (A ↦ ltyp) → ltyp ℓ
  Wᵒ : (A : ltyp ℓ) → (A ↦ finltyp) → ltyp ℓ
  Wᵒ_&_/_ : (A : ltyp ℓ) → (B : A ↦ finltyp) → ((a : W． A B) → Fraction A B a) → ltyp ℓ
  Listᵒ : (A : ltyp ℓ) → ltyp ℓ
  Listᵒ_/_ : (A : ltyp ℓ) → ((xs : List (A ．)) → ListFraction A xs) → ltyp ℓ

⟦ Ground A ⟧ = A , λ x → ι x
⟦ 𝟘ᵒ ⟧ = 𝟘 , λ ()
⟦ 𝟙ᵒ ⟧ = 𝟙 , (λ _ → ◇)
⟦ 𝟚ᵒ ⟧ = 𝟚 , (λ _ → ◇)
⟦ Πᵒ A m B ⟧ = ((x : A ．) → B x ．) , λ f → Λ⟨ x ∶ A ． ⟩ [ (x ∶ A) ^ m , f x ∶ B x ]
⟦ Π! A B ⟧ = ((x : A ．) → B x ．) , λ f → Λ⟨ x ∶ A ． ⟩ [ ! (x ∶ A) , f x ∶ B x ]
⟦ Σᵒ A m B ⟧ = Σ (A ．) (λ x → B x ．) , λ (x , y) → (x ∶ A) ^ m ⨾ y ∶ B x
⟦ Wᵒ A (B , Bfin) ⟧ = W (A ．) (λ x → B x ．) , recW (λ x Δ → (x ∶ A) ⨾ ⨂ (B x) (Bfin x) Δ )
⟦ Wᵒ_&_/_  A B m ⟧ = W (A ．) (λ x → B .fst x ．) , λ x → FractionSply A B x (m x)
⟦ Listᵒ A ⟧ = List (A ．) , foldr (λ x → x ∶ A ⨾_) ◇
⟦ Listᵒ A / m ⟧ = List (A ．) , λ xs → Listsply A xs (m xs)


const1 : (A : ltyp ℓ) (B : A ↦ finltyp) (x : W． A B) → FractionSply A B x (const A B x 1) ⇒ x ∶ Wᵒ A B
const1 A B (sup a f) = unitr ⨾ᶠ ⨂ᶠ (λ x → const1 A B (f x))



_⊩_ : sply ℓ → ltyp ℓ → ityp (ℓ-suc ℓ)
Δ ⊩ A = Σ⟨ a ∶ A ． ⟩ (Δ ⇒ a ∶ A)

infixl -100 _⊩_

module _ {Δ : sply ℓ} {A : ltyp ℓ} where
  real : Δ ⊩ A → A ．
  real (a , δ) = a


Idᵒ : (A : ltyp ℓ)
  → (a : A ．)
  → a ∶ A ⊩ A
Idᵒ A x = x , id

Cut : {Δ₀ Δ₁ : sply ℓ} {A B : ltyp ℓ}
  {m : ℕ}
  → ((a , _) : Δ₁ ⊩ A)
  → Δ₀ ⨾ (a ∶ A) ^ m ⊩ B
  → Δ₀ ⨾ Δ₁ ^ m ⊩ B
Cut (a , δ₀) (b , δ₁) = b , δ₁ ∘ id ⨾ᶠ ⇒^ _ δ₀

Coerce : {Δ₀ Δ₁ : sply ℓ} {A : ltyp ℓ}
  (δ : Δ₁ ⇒ Δ₀)
  → Δ₀ ⊩ A
  → Δ₁ ⊩ A
Coerce δ₀ (a , δ₁) = a , (δ₁ ∘ δ₀)

Convsply : {Δ₀ Δ₁ : sply ℓ} {A : ltyp ℓ}
  → Δ₀ ⊩ A
  → Δ₀ ≡ Δ₁
  → Δ₁ ⊩ A
Convsply (a , δ) refl = a , δ



-- Syntax for writing dependent linear function and pair types

infixr -9 Πᵒ
syntax Πᵒ A m (λ x → B) = ⟨ x ∈ A ⟩^ m ⊸ B

Πᵒnd : ltyp ℓ → ℕ → ltyp ℓ → ltyp ℓ
Πᵒnd A m B = Πᵒ A m (λ x → B)
infixr -9 Πᵒnd
syntax Πᵒnd A m B = ⟨ A ⟩^ m ⊸ B

Πᵒnd1 : ltyp ℓ → ltyp ℓ → ltyp ℓ
Πᵒnd1 A B = Πᵒ A 1 (λ x → B)
infixr -9 Πᵒnd1
syntax Πᵒnd1 A B = A ⊸ B


infixr -9 Π!
syntax Π! A (λ x → B) = !⟨ x ∈ A ⟩ ⊸ B

Π!nd : ltyp ℓ → ltyp ℓ → ltyp ℓ
Π!nd A B = Π! A (λ _ → B)
infixr -9 Π!nd
syntax Π!nd A B = !⟨ A ⟩ ⊸ B


infixr -9 Σᵒ
syntax Σᵒ A m (λ x → B) = ⟨ x ∈ A ⟩^ m ⊗ B


Σᵒnd : ltyp ℓ → ℕ → ltyp ℓ → ltyp ℓ
Σᵒnd A m B = Σᵒ A m (λ x → B)
infixr -9 Σᵒnd
syntax Σᵒnd A m B = ⟨ A ⟩^ m ⊗ B

Σᵒnd1 : ltyp ℓ → ltyp ℓ → ltyp ℓ
Σᵒnd1 A B = Σᵒ A 1 (λ x → B)
infixr -9 Σᵒnd1
syntax Σᵒnd1 A B = A ⊗ B




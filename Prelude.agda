{-# OPTIONS --safe #-}

module DLTT.Prelude where

open import Agda.Primitive public
  using    ( Level
  ; SSet )
  renaming ( lzero to ℓ-zero
  ; lsuc  to ℓ-suc
  ; _⊔_   to ℓ-max
  ; Set   to ityp
  ; Setω  to itypω )

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)

open import Agda.Builtin.Equality public

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω)

open import Agda.Builtin.Sigma public

open import Agda.Builtin.List public using (List; []; _∷_)


data 𝟘 {ℓ : Level} : Set ℓ where

data 𝟙 {ℓ : Level} : Set ℓ where
  tt* : 𝟙

open import Agda.Builtin.Equality public

≡subst : ∀{ℓ ℓ'}{A : Set ℓ} (P : A → Set ℓ') {x y : A} → x ≡ y → P x → P y
≡subst P refl p = p

private
  variable
    ℓ ℓ' ℓ'' : Level

natRec : {A : Set ℓ} → (A → A) → A → ℕ → A
natRec s n zero = n
natRec s n (suc m) = s (natRec s n m)


natElim : {A : ℕ → Set ℓ} → ((n : ℕ) → A n → A (suc n)) → A zero →
  (n : ℕ) → A n
natElim s z zero = z
natElim s z (suc m) = s m (natElim s z m)

infix 2 Σ-syntax
Σ-syntax : (A : Set ℓ) → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ⟨ x ∶ A ⟩ B

_×_ : ∀ (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ⟨ x ∶ A ⟩ B

ΣE : {A : ityp ℓ} {B : A → ityp ℓ'} {C : Σ A B → ityp (ℓ-suc (ℓ ⊔ ℓ'))}
  → ((x : A) → (y : B x) → C (x , y))
  → (z : Σ A B) → C z
ΣE f (x , y) = f x y


module _ {ℓ} {A : ityp ℓ} where
  len : List A → ℕ
  len [] = 0
  len (x ∷ xs) = 1 + len xs

  elimList : ∀ {ℓ'} {B : List A → ityp ℓ'}
    → B []
    → ((x : A) → {xs : List A} → B xs → B (x ∷ xs))
    → ∀ l → B l
  elimList b _ [] = b
  elimList {B = B} n c (x ∷ xs) = c x (elimList {B = B} n c xs)


module _ {A : ityp ℓ} {B : ityp ℓ'} where
  foldr : (A → B → B) → B → List A → B
  foldr c n []       = n
  foldr c n (x ∷ xs) = c x (foldr c n xs)


data 𝟚 {ℓ : Level} : ityp ℓ where
  false true : 𝟚

infix 0 if_then_else_

if_then_else_ : {A : 𝟚 {ℓ} → ityp ℓ} → (b : 𝟚) → A true → A false → A b
if true  then t else f = t
if false then t else f = f

if'_then_else_ : {A : ityp ℓ} → (b : 𝟚 {ℓ}) → A → A → A
if' true  then t else f = t
if' false then t else f = f


∣_∣ : 𝟚 {ℓ} → ℕ
∣ false ∣ = 0
∣ true ∣ = 1


_∧_ : 𝟚 {ℓ} → 𝟚 → 𝟚 {ℓ}
false ∧ b = false
true ∧ b = b

¬_ : 𝟚 {ℓ} → 𝟚 {ℓ}
¬ true = false
¬ false = true

data Dec (P : ityp ℓ) : ityp ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : (P → 𝟘 {ℓ})) → Dec P


𝟘? : List (𝟘 {ℓ})
𝟘? = []

𝟙? : List (𝟙 {ℓ})
𝟙? = tt* ∷ []

𝟚? : List (𝟚 {ℓ})
𝟚? = false ∷ true ∷ []

elimΣ : ∀{ℓ} {A : ityp ℓ} {B : A → ityp ℓ} {C : Σ A B → ityp ℓ}
  → ((x : A) → (y : B x) → C (x , y))
  → (z : Σ A B) → C z
elimΣ f (x , y) = f x y

data W {ℓ ℓ' : Level} (A : ityp ℓ) (B : A → ityp ℓ') : ityp (ℓ-max ℓ ℓ') where
  sup : (a : A) → ((b : B a) → W A B) → W A B


elimW
  : {A : Set ℓ}
  → {B : A → Set ℓ'}
  → {P : W A B → Set ℓ''}
  → ((a : A) (f : B a → W A B) → (g : (b : B a) → P (f b)) → P (sup a f))
  → (w : W A B)
  → P w
elimW {P = P} step (sup a f) = step a f (λ b → elimW {P = P} step (f b))

recW
  : {A : Set ℓ} {B : A → Set ℓ}
  → {C : Set ℓ'}
  → ((a : A) (g : B a → C) → C)
  → W A B → C
recW step = elimW (λ a f ih → step a (λ b → ih b))

_＋_ : (A B : ityp ℓ) → ityp ℓ
_＋_ {ℓ} A B = Σ (𝟚 {ℓ}) (λ {true → A ; false → B})



data _≤_ : ℕ → ℕ → ityp where
  z≤n : {n : ℕ} → 0 ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤refl : (n : ℕ) → n ≤ n
≤refl zero = z≤n
≤refl (suc n) = s≤s (≤refl n)

≤suc : {m n : ℕ} → m ≤ n → m ≤ suc n
≤suc z≤n = z≤n
≤suc (s≤s l) = s≤s (≤suc l)

ltℕ : ℕ → ℕ → 𝟚 {ℓ-zero}
ltℕ _ zero = false
ltℕ zero (suc _) = true
ltℕ (suc m) (suc n) = ltℕ m n

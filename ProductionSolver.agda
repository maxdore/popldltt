{-# OPTIONS --safe #-}

module DLTT.ProductionSolver where

-- A simple solver for coercions between supplies which only differ in the
-- order and bracketing of their components and in occurrences of ◇, i.e. it
-- constructs productions from the symmetric monoidal structure of supplies.

open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection
  hiding (Type)

open import DLTT.Base


-- Syntax of supplies built from atoms, ◇ and _⨾_

infixr -12 _⊙_

data Expr : ityp where
  atom : ℕ → Expr
  unit : Expr
  _⊙_  : Expr → Expr → Expr

eqℕ? : (m n : ℕ) → Maybe (m ≡ n)
eqℕ? zero    zero    = just refl
eqℕ? (suc m) (suc n) with eqℕ? m n
... | just refl = just refl
... | nothing   = nothing
eqℕ? _       _       = nothing

mapMaybe : ∀ {ℓ ℓ'} {A : ityp ℓ} {B : ityp ℓ'} → (A → B) → Maybe A → Maybe B
mapMaybe f (just x) = just (f x)
mapMaybe f nothing  = nothing

FromJust : ∀ {ℓ} {A : ityp ℓ} → Maybe A → ityp ℓ
FromJust {A = A} (just _) = A
FromJust         nothing  = 𝟙

fromJust : ∀ {ℓ} {A : ityp ℓ} (m : Maybe A) → FromJust m
fromJust (just x) = x
fromJust nothing  = tt*


-- Interpretation in an environment of atoms and normalisation

module _ {ℓ : Level} (env : List (sply ℓ)) where

  private
    -- lookup with a default, out of range indices are never generated
    at : List (sply ℓ) → ℕ → sply ℓ
    at []       _       = ◇
    at (Δ ∷ _)  zero    = Δ
    at (_ ∷ Δs) (suc n) = at Δs n

  ⟦_⟧ₐ : ℕ → sply ℓ
  ⟦ n ⟧ₐ = at env n

  ⟦_⟧ₑ : Expr → sply ℓ
  ⟦ atom n ⟧ₑ = ⟦ n ⟧ₐ
  ⟦ unit   ⟧ₑ = ◇
  ⟦ e ⊙ e' ⟧ₑ = ⟦ e ⟧ₑ ⨾ ⟦ e' ⟧ₑ

  -- Normal forms are right-nested lists of atoms terminated by ◇
  ⟦_⟧ₗ : List ℕ → sply ℓ
  ⟦ []     ⟧ₗ = ◇
  ⟦ n ∷ ns ⟧ₗ = ⟦ n ⟧ₐ ⨾ ⟦ ns ⟧ₗ

  flatten : Expr → List ℕ → List ℕ
  flatten (atom n) ns = n ∷ ns
  flatten unit     ns = ns
  flatten (e ⊙ e') ns = flatten e (flatten e' ns)

  toNF : (e : Expr) (ns : List ℕ) → ⟦ e ⟧ₑ ⨾ ⟦ ns ⟧ₗ ⇒ ⟦ flatten e ns ⟧ₗ
  toNF (atom n) ns = id
  toNF unit     ns = unitl
  toNF (e ⊙ e') ns = toNF e (flatten e' ns) ∘ id ⨾ᶠ toNF e' ns ∘ assoc'

  fromNF : (e : Expr) (ns : List ℕ) → ⟦ flatten e ns ⟧ₗ ⇒ ⟦ e ⟧ₑ ⨾ ⟦ ns ⟧ₗ
  fromNF (atom n) ns = id
  fromNF unit     ns = unitl'
  fromNF (e ⊙ e') ns = assoc ∘ id ⨾ᶠ fromNF e' ns ∘ fromNF e (flatten e' ns)

  toNormal : (e : Expr) → ⟦ e ⟧ₑ ⇒ ⟦ flatten e [] ⟧ₗ
  toNormal e = toNF e [] ∘ unitr'

  fromNormal : (e : Expr) → ⟦ flatten e [] ⟧ₗ ⇒ ⟦ e ⟧ₑ
  fromNormal e = unitr ∘ fromNF e []

  -- Moving the first occurrence of an atom to the front
  pick : (n : ℕ) (ns : List ℕ) → Maybe (Σ⟨ ms ∶ List ℕ ⟩ (⟦ ns ⟧ₗ ⇒ ⟦ n ∷ ms ⟧ₗ))
  pick n []       = nothing
  pick n (m ∷ ns) with eqℕ? n m
  ... | just refl = just (ns , id)
  ... | nothing   = mapMaybe
    (λ (ms , δ) → m ∷ ms , assoc' ∘ swap ⨾ᶠ id ∘ assoc ∘ id ⨾ᶠ δ)
    (pick n ns)

  -- Productions between permutations of lists of atoms
  permute : (ns ms : List ℕ) → Maybe (⟦ ns ⟧ₗ ⇒ ⟦ ms ⟧ₗ)
  permute []      []       = just id
  permute (_ ∷ _) []       = nothing
  permute ns      (m ∷ ms) with pick m ns
  ... | nothing        = nothing
  ... | just (ns' , δ) = mapMaybe (λ δ' → id ⨾ᶠ δ' ∘ δ) (permute ns' ms)

  prove : (e₀ e₁ : Expr) → Maybe (⟦ e₀ ⟧ₑ ⇒ ⟦ e₁ ⟧ₑ)
  prove e₀ e₁ = mapMaybe
    (λ δ → fromNormal e₁ ∘ δ ∘ toNormal e₀)
    (permute (flatten e₀ []) (flatten e₁ []))


-- Reflection machinery

private
  infixl 1 _>>=_ _>>_

  _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  _>>=_ = bindTC

  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
  m >> m' = m >>= λ _ → m'

  vArg hArg : ∀ {a} {A : Set a} → A → Arg A
  vArg = arg (arg-info visible (modality relevant quantity-ω))
  hArg = arg (arg-info hidden  (modality relevant quantity-ω))

  -- Definitional equality of atoms, without committing to any solved metas
  -- if the atoms are not equal
  equalTerms : Term → Term → TC Bool
  equalTerms t t' = runSpeculative
    (catchTC (noConstraints (unify t t') >> returnTC (true , true))
             (returnTC (false , false)))

  -- Index of an atom in the list of atoms collected so far, extending the list
  -- if it has not been seen yet
  indexOf : Term → List Term → TC (ℕ × List Term)
  indexOf t []        = returnTC (0 , t ∷ [])
  indexOf t (t' ∷ ts) = equalTerms t t' >>= λ where
    true  → returnTC (0 , t' ∷ ts)
    false → indexOf t ts >>= λ (n , ts') → returnTC (suc n , t' ∷ ts')

  -- Reading off the syntax of a supply. Constructors carry the level as hidden
  -- parameter, which we skip.
  reify : Term → List Term → TC (Expr × List Term)
  reify (con (quote ◇) _) ts = returnTC (unit , ts)
  reify (con (quote _⨾_) (_ ∷ arg _ Δ₀ ∷ arg _ Δ₁ ∷ [])) ts =
    reify Δ₀ ts >>= λ (e₀ , ts) →
    reify Δ₁ ts >>= λ (e₁ , ts) →
    returnTC ((e₀ ⊙ e₁) , ts)
  reify (meta m _) ts = blockOnMeta m
  reify Δ ts =
    indexOf Δ ts >>= λ (n , ts) → returnTC (atom n , ts)

  quoteℕ : ℕ → Term
  quoteℕ n = lit (nat n)

  quoteExpr : Expr → Term
  quoteExpr (atom n) = con (quote atom) (vArg (quoteℕ n) ∷ [])
  quoteExpr unit     = con (quote unit) []
  quoteExpr (e ⊙ e') = con (quote _⊙_) (vArg (quoteExpr e) ∷ vArg (quoteExpr e') ∷ [])

  quoteList : List Term → Term
  quoteList []       = con (quote []) []
  quoteList (t ∷ ts) = con (quote _∷_) (vArg t ∷ vArg (quoteList ts) ∷ [])

  solveGoal : Term → Term → TC ⊤
  solveGoal hole (def (quote _⇒_) (arg _ ℓ ∷ arg _ Δ₀ ∷ arg _ Δ₁ ∷ [])) =
    reify Δ₀ []  >>= λ (e₀ , ts) →
    reify Δ₁ ts  >>= λ (e₁ , ts) →
    catchTC
      (unify hole
        (def (quote fromJust)
          (vArg (def (quote prove)
            (hArg ℓ ∷ vArg (quoteList ts) ∷ vArg (quoteExpr e₀) ∷ vArg (quoteExpr e₁) ∷ []))
          ∷ [])))
      (typeError (strErr "solve: the supplies " ∷ termErr Δ₀ ∷ strErr " and "
        ∷ termErr Δ₁ ∷ strErr " do not consist of the same components" ∷ []))
  solveGoal hole (meta m _) = blockOnMeta m
  solveGoal hole goal = typeError
    (strErr "solve: goal is not a production Δ₀ ⇒ Δ₁: " ∷ termErr goal ∷ [])

macro
  -- Solves a goal Δ₀ ⇒ Δ₁ if Δ₁ arises from Δ₀ by rebracketing, reordering and
  -- adding or removing ◇. Components which are not ◇ or _⨾_ are treated as
  -- atoms and compared up to definitional equality.
  solve : Term → TC ⊤
  solve hole = inferType hole >>= normalise >>= solveGoal hole

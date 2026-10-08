{-# OPTIONS --safe #-}

module DLTT.Everything where

open import DLTT.Prelude

-- Contains the main construction: definition of supply and production types,
-- linear type formers and their elaboration, introduces quantitative features
-- with supply exponentiation
open import DLTT.Base

-- Formalises elaborations of the linear type formers
open import DLTT.Function
open import DLTT.Pair
open import DLTT.Empty
open import DLTT.Unit
open import DLTT.Bool
open import DLTT.W

-- Examples highlighting basic workings of the embedded linear structure
open import DLTT.Examples.Structure

-- Functional programming examples, concluding with substitution function in
-- lambda calculus
open import DLTT.Examples.Maybe
open import DLTT.Examples.List
open import DLTT.Examples.Quicksort
open import DLTT.Examples.Nat
open import DLTT.Examples.Lambda

-- Tactic with simple monoidal solver to resolve basic coercions, and examples
open import DLTT.ProductionSolver
open import DLTT.Examples.Solver

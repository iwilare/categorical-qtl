{-# OPTIONS --sized-types #-}

open import Counterpart.Categorical.TemporalModel using (TemporalCounterpartWModel)
open import SortedAlgebra using (Signature)

module Counterpart.Categorical.QLTL.ClassicalAttributes {ℓ} {Σ : Signature {ℓ}} (M : TemporalCounterpartWModel Σ) where

open import Data.Nat using (ℕ)
open import Level using (_⊔_) renaming (suc to sucℓ)
open import Relation.Unary using (Pred; _∈_)
open import Size using (Size; ∞; ↑_; Size<_)
open import Data.Product using (∃-syntax; _×_)

open import Categories.Category
open import Counterpart.Categorical.TemporalStructure using (TemporalStructure)
open import Categories.Functor using (Functor)
open import RelPresheaves using (RelPresheaf)

open import Counterpart.Categorical.QLTL.Predicates

module M = TemporalCounterpartWModel M

open Category M.W
open TemporalStructure M.T
open import Counterpart.Categorical.ClassicalAttribute M.W public

module _ (X : RelPresheaf M.W) where
  private module X = Functor X

  -- Shorthand for:
  --   "There exists a counterpart for s in the
  --    path p after i steps which satisfies A"
  at∃ : ∀ {ω} → Path ω ∞ → X.₀ ω → ClassicalAttribute X → ℕ → Set _
  at∃ p s A i = ∃[ z ] X.₁ (compose≤ p i) z s × z ∈ A

  -- Shorthand for:
  --   "All counterparts of s in the path p
  --    after i steps satisfy A"
  at∀ : ∀ {ω} → Path ω ∞ → X.₀ ω → ClassicalAttribute X → ℕ → Set _
  at∀ p s A i = ∀ z → X.₁ (compose≤ p i) z s → z ∈ A

  XO : ClassicalAttribute X → ClassicalAttribute X
  XO A s = ∀ {σ}
          → (ρ : _ ⇒ σ)
          → {ρ ∈ T}
          → ∃[ z ] X.₁ ρ z s × s ∈ A

  XA : ClassicalAttribute X → ClassicalAttribute X
  XA A s = ∀ {σ}
          → (ρ : _ ⇒ σ)
          → {ρ ∈ T}
          → ∀ z → X.₁ ρ z s → s ∈ A

  XU : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  XU A B {ω} s = ∀ (p : Path ω ∞) → (at∃ p s A) until (at∃ p s B)

  XF : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  XF A B {ω} s = ∀ (p : Path ω ∞) → (at∀ p s A) until (at∀ p s B)

  XW : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  XW A B {ω} s = ∀ (p : Path ω ∞) → (at∃ p s A) weakUntil (at∃ p s B)

  XT : ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  XT A B {ω} s = ∀ (p : Path ω ∞) → (at∀ p s A) weakUntil (at∀ p s B)

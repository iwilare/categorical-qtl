{-# OPTIONS --sized-types #-}

module Counterpart.Categorical.QLTL.Predicates where

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (Pred; _∈_)

-- A holds for all i strictly before n steps
_before_ : ∀ {ℓ} (A : Pred ℕ ℓ) → Pred ℕ ℓ
A before n = ∀ i → i < n → i ∈ A

-- A holds until B is satisfied
_until_ : ∀ {ℓ} (A B : Pred ℕ ℓ) → Set ℓ
A until B = ∃[ n ] (A before n × n ∈ B)

-- A is always satisfied at each step
always : ∀ {ℓ} (A : Pred ℕ ℓ) → Set ℓ
always A = ∀ i → i ∈ A

-- Either until or always hold
_weakUntil_ : ∀ {ℓ} (A B : Pred ℕ ℓ) → Set ℓ
A weakUntil B = A until B ⊎ always A


-- There exists a step after which A is satisfied
eventually : ∀ {ℓ} (A : Pred ℕ ℓ) → Set ℓ
eventually A = ∃[ i ] i ∈ A

{-# OPTIONS --sized-types #-}

module Counterpart.Classical {ℓ} where

open import Level using () renaming (suc to sucℓ)
open import Relation.Binary using (REL; Rel)

open import SortedAlgebra using (Signature; Σ-Algebra; Σ-Rel)

record LewisCounterpartModel : Set (sucℓ ℓ) where
  field
      W : Set ℓ
      D : W → Set ℓ
      R : Rel W ℓ
      C : ∀ {w₁ w₂}
        → R w₁ w₂
        → REL (D w₁) (D w₂) ℓ

record CounterpartModel (Σ : Signature {ℓ}) : Set (sucℓ ℓ)  where
  field
      W : Set ℓ
      d : W → Σ-Algebra Σ
      _⇝_ : Rel W ℓ
      f : ∀ {w₁ w₂}
        → w₁ ⇝ w₂
        → Σ-Rel (d w₁) (d w₂)
{-# OPTIONS --sized-types #-}

open import Categories.Category
open import Counterpart.Categorical.TemporalStructure

module Counterpart.Categorical.ClassicalAttribute {co cℓ ce} (W : Category co cℓ ce) where

open import Level using (_⊔_) renaming (suc to sucℓ)
open import Relation.Unary using (Pred)

open import Categories.Functor

open import RelPresheaves using (RelPresheaf)

ClassicalAttribute : RelPresheaf W → Set (sucℓ (co ⊔ cℓ ⊔ ce))
ClassicalAttribute X = ∀ {ω} → Pred (X.₀ ω) _
  where module X = Functor X


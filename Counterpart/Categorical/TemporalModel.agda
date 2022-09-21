{-# OPTIONS --sized-types #-}

module Counterpart.Categorical.TemporalModel where

open import Level using () renaming (suc to sucℓ)

open import Counterpart.Categorical
open import SortedAlgebra using (Signature)
open import Counterpart.Categorical.TemporalStructure

record TemporalCounterpartWModel {ℓ} (Σ : Signature {ℓ}) : Set (sucℓ ℓ) where
  field
    M : CounterpartWModel Σ

  open CounterpartWModel M public
  
  field
    T : TemporalStructure W
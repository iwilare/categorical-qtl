{-# OPTIONS --sized-types #-}

open import Level
open import Relation.Binary

open import SortedAlgebra
open import DVec
import RelPresheaves

open import Data.Vec as V using () renaming (Vec to Vector)
open import Data.Product using (_,_; proj₁; proj₂; <_,_>)
open import Data.Fin using (Fin)
open import Data.Unit.Polymorphic hiding (tt)
open import Data.Unit.Base using (tt)

record CounterpartFrame {ℓ} : Set (suc ℓ) where
  field
    W : Set ℓ
    D : W → Set ℓ
    R : Rel W ℓ
    C : ∀ {w₁ w₂}
      → R w₁ w₂
      → REL (D w₁) (D w₂) ℓ

record CounterpartModel {ℓ} (SΣ : Signature {ℓ}) : Set (suc ℓ)  where
  open Signature SΣ
  field
    W   : Set ℓ
    d   : W → Σ-Algebra SΣ
    _⇝_ : Rel W ℓ
    Σ[_] : ∀ {w₁ w₂}
         → w₁ ⇝ w₂
         → Σ-Homorel (d w₁) (d w₂)

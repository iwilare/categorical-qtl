{-# OPTIONS --sized-types #-}

open import Level
open import Relation.Binary
open import Categories.Category
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Rels
open import Categories.Functor.Presheaf
open import Categories.Category.Construction.Properties.Presheaves.Cartesian as C
open C.IsCartesian
open import Categories.Category.Complete
open import Categories.Category.Complete.Finitely
open import Categories.Category.Complete.Properties
open import Categories.Category.BinaryProducts
open import Categories.Object.Terminal

open import SortedAlgebra
open import DVec
open import RelPresheaves

open import Data.Vec.Functional using (foldl)

record CounterpartFrame {ℓ} : Set (suc ℓ) where
  field
    W : Set ℓ
    D : W → Set ℓ
    R : Rel W ℓ
    C : (w₁ : W) → (w₂ : W) → REL (D w₁) (D w₂) ℓ

record CounterpartModel (Σ : Signature) {ℓ} : Set (suc ℓ)  where
  field
    W      : Set ℓ
    d      : W → Σ-Algebra Σ
    _⇝_[_] : (w₁ : W) → (w₂ : W) → (cr : Σ-Homomorphism Σ (d w₁) (d w₂)) → Set ℓ




record CounterpartWPresheaf (SΣ : Signature) {o} {ℓ} {e} : Set (suc o ⊔ suc ℓ ⊔ suc e)  where

  open Signature SΣ

  field
    W : Category o ℓ e

  open Cartesian (Presheaves-Cartesian W o ℓ)
  open BinaryProducts products
  open Terminal terminal

  field
    D : Σ → RelPresheaf W
    F : dmap (λ { F< _ , τ* , τ > → {!   !} }) 𝓕
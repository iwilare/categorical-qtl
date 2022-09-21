{-# OPTIONS --sized-types #-}

open import SortedAlgebra using (Signature; Σ-Algebra; Σ-Rel) 

module Counterpart.CategoricalToClassical {ℓ} {Σ : Signature {ℓ}} where

import Data.Quiver.Paths

open import Categories.Functor  using (Functor)
open import Categories.Category using (_[_≈_])
open import Categories.Category using (Category)
open import Categories.Category.Construction.PathCategory using (PathCategory)
open import Categories.Category.Instance.Rels using (Rels)

open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (_,_; Σ-syntax; proj₁)
open import Function using (id; flip)
open import Relation.Unary using (_∈_)
open import Level using (lift)
open import Relation.Binary using (REL)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)

open import Counterpart.Categorical.TemporalModel
open import Counterpart.Categorical.TemporalStructure
open import Counterpart.Categorical
open import Counterpart.Classical
open import RelPresheaves
open import VecT

CategorifyModel : TemporalCounterpartWModel Σ
                → CounterpartModel Σ
CategorifyModel M =
  record
    { W = Obj
    ; d = λ ω →
            record
              { S = λ Σ → Functor.₀ M.⟦ Σ ⟧ ω
              ; F = λ 𝑓 → RelPresheaf⇒.η (I 𝑓)
              }
    ; _⇝_ = λ a b → Σ[ t ∈ (a ⇒ b) ] (t ∈ T)
    ; f = λ x →
                record
                  { ρ = λ {τ} → flip (Functor.₁ ⟦ τ ⟧ (proj₁ x) )
                  ; ρ-homo = λ f z → RelPresheaf⇒.imply (I f) (VecT.op z)
                  }
    } where module M = TemporalCounterpartWModel M
            open Signature Σ
            open Category M.W
            open TemporalStructure M.T
            open CounterpartWModel M.M
{-# OPTIONS --sized-types #-}

open import SortedAlgebra
open import Counterpart.Categorical.TemporalModel

module Counterpart.Categorical.LTL.Semantics {ℓ} {Σ : Signature {ℓ}}
               (M : TemporalCounterpartWModel Σ) where

open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (_∈_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)

open import Categories.Functor

open import RelPresheaves

open Signature Σ
open SortedAlgebra.Term Σ
open import LTL
open Functor using (F₀)
open TemporalCounterpartWModel M using (⟦_⟧*; ⟦_⟧ᵗ)
open RelPresheaf⇒ using (η)

open import Counterpart.Categorical.LTL.ClassicalAttributes M

⟨_⟩ : ∀ {n} {Γ : Ctx n} → LTL Γ → ClassicalAttribute (⟦ Γ ⟧*)
⟨ true         ⟩ a = ⊤
⟨ false        ⟩ a = ⊥
⟨ ! ϕ          ⟩ a = ¬ ⟨ ϕ ⟩ a
⟨ ϕ₁ ∧ ϕ₂      ⟩ a = ⟨ ϕ₁ ⟩ a × ⟨ ϕ₂ ⟩ a
⟨ ϕ₁ ∨ ϕ₂      ⟩ a = ⟨ ϕ₁ ⟩ a ⊎ ⟨ ϕ₂ ⟩ a
⟨ ∃< τ > ϕ     ⟩ a = ∃[ b ] ⟨ ϕ ⟩ (b , a)
⟨ ∀< τ > ϕ     ⟩ a = ∀ b  → ⟨ ϕ ⟩ (b , a)
⟨ t₁ ≡ᵗ t₂     ⟩ a = η (⟦ t₁ ⟧ᵗ) a ≡ η (⟦ t₂ ⟧ᵗ) a
⟨ t₁ ≢ᵗ t₂     ⟩ a = η (⟦ t₁ ⟧ᵗ) a ≢ η (⟦ t₂ ⟧ᵗ) a
⟨ O ϕ         ⟩ = XO (⟦ _ ⟧*) ⟨ ϕ ⟩
⟨ A ϕ         ⟩ = XA (⟦ _ ⟧*) ⟨ ϕ ⟩
⟨ ϕ₁ U ϕ₂     ⟩ = XU (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
⟨ ϕ₁ F ϕ₂     ⟩ = XF (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
⟨ ϕ₁ W ϕ₂     ⟩ = XW (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
⟨ ϕ₁ T ϕ₂     ⟩ = XT (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩

DecidableFormula : ∀ {n} {Γ : Ctx n} → LTL Γ → Set ℓ
DecidableFormula {_} {Γ} ϕ = ∀ ω (a : F₀ (⟦ Γ ⟧*) ω) → Dec (a ∈ ⟨ ϕ ⟩)

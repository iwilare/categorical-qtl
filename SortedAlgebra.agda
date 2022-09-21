{-# OPTIONS --sized-types #-}

module SortedAlgebra {ℓ} where

import Function 
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Level using () renaming (suc to sucℓ)
open import Relation.Binary using (REL)
open import Size

open import VecT using (zip; mapT; map)

record FunctionSignature (𝓢 : Set ℓ) : Set ℓ where
  constructor _↦_
  field
      {arity} : ℕ
      τ*      : Vec 𝓢 arity
      τ       : 𝓢

infix 4 _↦_

record Signature : Set (sucℓ ℓ) where

  open FunctionSignature

  field
    𝓢 : Set ℓ
    𝓕 : Set ℓ
    sign𝓕 : 𝓕 → FunctionSignature 𝓢

  open Function using (_∘_)

  args = τ* ∘ sign𝓕
  ret  = τ  ∘ sign𝓕

record Σ-Algebra (Σ : Signature) : Set (sucℓ ℓ) where

  open Signature Σ

  field
    S : 𝓢 → Set ℓ

  argType : 𝓕 → Set ℓ
  argType f = mapT S (args f)

  retType : 𝓕 → Set ℓ
  retType f = S (ret f)

  field
    F : ∀ (f : 𝓕) → argType f → retType f

record Σ-Rel {Σ} (A : Σ-Algebra Σ) (B : Σ-Algebra Σ) : Set (sucℓ ℓ) where

  open Signature Σ
  open Function using (_∘_; flip)

  private
    module A = Σ-Algebra A
    module B = Σ-Algebra B

  field
    ρ      : ∀ {τ} → REL (A.S τ) (B.S τ) ℓ
    ρ-homo :
      ∀ (f : 𝓕)
      → {as : A.argType f}
      → {bs : B.argType f}
      → zip ρ as bs
      → ρ (A.F f as) (B.F f bs)

  op : Σ-Rel B A
  op = record { ρ = flip ρ 
              ; ρ-homo = λ f → ρ-homo f ∘ VecT.op
              }

module Term (Σ : Signature) where

  open Signature Σ

  Ctx : ℕ → Set ℓ
  Ctx = Vec 𝓢

  data _⊢_⟨_⟩ {n} Γ : 𝓢 → Size → Set ℓ where
    var : (i : Fin n)
        → Γ ⊢ lookup Γ i ⟨ ∞ ⟩

    fun : ∀ {s}
        → (f : 𝓕)
        → mapT (Γ ⊢_⟨ s ⟩) (args f)
        → Γ ⊢ ret f ⟨ ↑ s ⟩

  Subst : ∀ {n m} → Ctx n → Ctx m → Set ℓ
  Subst Γ Δ = ∀ i → Δ ⊢ lookup Γ i ⟨ ∞ ⟩

  sub : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m}
      → Subst Γ Δ
      → (∀ {s A} → Γ ⊢ A ⟨ s ⟩ → Δ ⊢ A ⟨ s ⟩)
  sub σ (var x)   = σ x
  sub σ (fun f x) = fun f (map (sub σ) x)

  id : ∀ {n} {Γ : Ctx n} → Subst Γ Γ
  id i = var i

  _∘_ : ∀ {n m o} {A : Ctx n} {B : Ctx m} {C : Ctx o}
      → Subst B C → Subst A B → Subst A C
  (f ∘ g) i = sub f (g i)

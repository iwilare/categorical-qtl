{-# OPTIONS --sized-types #-}

open import Level
open import SortedAlgebra using (Signature; module Terms)

module LTL {ℓ} (SΣ : Signature {ℓ}) where

open Terms SΣ hiding (_⊢_)
open Signature SΣ

open import RelPresheaves

infix 30 ◯_

data [_] : Ctx → Set ℓ where
  ⊤   : ∀ {Γ} → [ Γ ]
  _∧_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
  _∨_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
  _U_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
  _W_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
  ◯_  : ∀ {Γ} → [ Γ ] → [ Γ ]
  ∃[_]_ : ∀ {Γ}
      → (τ : Σ)
      → [ τ ∷ Γ ]
      → [     Γ ]
  ∀[_]_ : ∀ {Γ}
      → (τ : Σ)
      → [ τ ∷ Γ ]
      → [     Γ ]
  [_]_≡_ : ∀ {Γ i}
      → (τ : Σ)
      → Γ ⊢ τ ⟦ i ⟧
      → Γ ⊢ τ ⟦ i ⟧
      → [ Γ ]
  [_]_≢_ : ∀ {Γ i}
      → (τ : Σ)
      → Γ ⊢ τ ⟦ i ⟧
      → Γ ⊢ τ ⟦ i ⟧
      → [ Γ ]

--data _⊨_ : {Γ} → [ Γ ]* → [ Γ ] → Set ℓ where
--  _⊨_ : ∀ {Γ} → [ Γ ] → [ Γ ] → _⊨_
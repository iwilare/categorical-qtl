{-# OPTIONS --sized-types #-}

open import SortedAlgebra using (Signature)

module LTL {ℓ} {Σ : Signature {ℓ}} where

open import Data.Vec using (_∷_)

open Signature Σ
open SortedAlgebra.Term Σ

data LTL {n} (Γ : Ctx n) : Set ℓ where
  true  : LTL Γ
  false : LTL Γ
  !_    : LTL Γ → LTL Γ
  _∧_   : LTL Γ → LTL Γ → LTL Γ
  _∨_   : LTL Γ → LTL Γ → LTL Γ
  O_    : LTL Γ → LTL Γ
  A_    : LTL Γ → LTL Γ
  _F_   : LTL Γ → LTL Γ → LTL Γ
  _U_   : LTL Γ → LTL Γ → LTL Γ
  _W_   : LTL Γ → LTL Γ → LTL Γ
  _T_   : LTL Γ → LTL Γ → LTL Γ
  ∃<_>_ : (τ : 𝓢)
        → LTL (τ ∷ Γ)
        → LTL Γ
  ∀<_>_ : (τ : 𝓢)
        → LTL (τ ∷ Γ)
        → LTL Γ
  _≡ᵗ_  : ∀ {i τ}
        → Γ ⊢ τ ⟨ i ⟩
        → Γ ⊢ τ ⟨ i ⟩
        → LTL Γ
  _≢ᵗ_  : ∀ {i τ}
        → Γ ⊢ τ ⟨ i ⟩
        → Γ ⊢ τ ⟨ i ⟩
        → LTL Γ

◇_ : ∀ {n} {Γ : Ctx n} → LTL Γ → LTL Γ
◇ ϕ = true U ϕ

□_ : ∀ {n} {Γ : Ctx n} → LTL Γ → LTL Γ
□ ϕ = ϕ W false

◇*_ : ∀ {n} {Γ : Ctx n} → LTL Γ → LTL Γ
◇* ϕ = true F ϕ

□*_ : ∀ {n} {Γ : Ctx n} → LTL Γ → LTL Γ
□* ϕ = ϕ T false

infix 15 _∧_ _∨_
infix 20 ◇_ □_ ◇*_ □*_ O_ A_ _U_ _F_ _W_ _T_
infix 23 ∃<_>_ ∀<_>_
infix 25 _≡ᵗ_ _≢ᵗ_

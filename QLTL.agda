{-# OPTIONS --sized-types #-}

open import SortedAlgebra using (Signature)

module QLTL {ℓ} {Σ : Signature {ℓ}} where

open import Data.Vec using (_∷_)

open Signature Σ
open SortedAlgebra.Term Σ

data QLTL {n} (Γ : Ctx n) : Set ℓ where
  true  : QLTL Γ
  false : QLTL Γ
  !_    : QLTL Γ → QLTL Γ
  _∧_   : QLTL Γ → QLTL Γ → QLTL Γ
  _∨_   : QLTL Γ → QLTL Γ → QLTL Γ
  O_    : QLTL Γ → QLTL Γ
  A_    : QLTL Γ → QLTL Γ
  _F_   : QLTL Γ → QLTL Γ → QLTL Γ
  _U_   : QLTL Γ → QLTL Γ → QLTL Γ
  _W_   : QLTL Γ → QLTL Γ → QLTL Γ
  _T_   : QLTL Γ → QLTL Γ → QLTL Γ
  ∃<_>_ : (τ : 𝓢)
        → QLTL (τ ∷ Γ)
        → QLTL Γ
  ∀<_>_ : (τ : 𝓢)
        → QLTL (τ ∷ Γ)
        → QLTL Γ
  _≡ᵗ_  : ∀ {i τ}
        → Γ ⊢ τ ⟨ i ⟩
        → Γ ⊢ τ ⟨ i ⟩
        → QLTL Γ
  _≢ᵗ_  : ∀ {i τ}
        → Γ ⊢ τ ⟨ i ⟩
        → Γ ⊢ τ ⟨ i ⟩
        → QLTL Γ

◇_ : ∀ {n} {Γ : Ctx n} → QLTL Γ → QLTL Γ
◇ ϕ = true U ϕ

□_ : ∀ {n} {Γ : Ctx n} → QLTL Γ → QLTL Γ
□ ϕ = ϕ W false

◇*_ : ∀ {n} {Γ : Ctx n} → QLTL Γ → QLTL Γ
◇* ϕ = true F ϕ

□*_ : ∀ {n} {Γ : Ctx n} → QLTL Γ → QLTL Γ
□* ϕ = ϕ T false

infix 15 _∧_ _∨_
infix 20 ◇_ □_ ◇*_ □*_ O_ A_ _U_ _F_ _W_ _T_
infix 23 ∃<_>_ ∀<_>_
infix 25 _≡ᵗ_ _≢ᵗ_

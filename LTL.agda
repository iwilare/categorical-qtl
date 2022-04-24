{-# OPTIONS --sized-types #-}

open import Size
open import Level

open import Data.Nat     using (ℕ; _≤_)
open import Data.Product using (∃-syntax; _,_; -,_; _×_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Categories.Category
open import Categories.Functor

open import SortedAlgebra using (Signature; module Terms)
open import RelPresheaves
open import CounterpartCategorical
open import TemporalStructure
open import DVec

module LTL {ℓ} {SΣ : Signature {ℓ}} (ℑ : CounterpartWModel SΣ) (T : TemporalStructure (CounterpartWModel.W ℑ)) where
  open CounterpartWModel ℑ
  open Signature SΣ
  open Terms SΣ
  open TemporalStructure.TemporalStructure T
  open RelPresheaf⇒
  open Category W

  data [_] : Ctx → Set ℓ where
    true : ∀ {Γ} → [ Γ ]
    _∧_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _∨_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _U_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    ∃◯_ : ∀ {Γ} → [ Γ ] → [ Γ ]
    ∀◯_ : ∀ {Γ} → [ Γ ] → [ Γ ]
    ◇_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    □_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    ∃<_>_ : ∀ {n} {Γ : Vec Σ n}
        → (τ : Σ)
        → [ -, τ ∷ Γ ]
        → [ -,     Γ ]
    ∀<_>_ : ∀ {n} {Γ : Vec Σ n}
        → (τ : Σ)
        → [ -, τ ∷ Γ ]
        → [ -,     Γ ]
    _≡ᵗ_ : ∀ {Γ i}
        → {τ : Σ}
        → Γ ⊢ τ ⟨ i ⟩
        → Γ ⊢ τ ⟨ i ⟩
        → [ Γ ]
    _≢ᵗ_ : ∀ {Γ i}
        → {τ : Σ}
        → Γ ⊢ τ ⟨ i ⟩
        → Γ ⊢ τ ⟨ i ⟩
        → [ Γ ]

  infix 15 _∧_ _∨_
  infix 20 ◇_ □_ ∃◯_ ∀◯_ _U_
  infix 23 ∃<_>_ ∀<_>_
  infix 25 _≡ᵗ_ _≢ᵗ_

  ⟦_⟧*₀ : ∀ {n} (Γ : Vec Σ n) ω → Set ℓ
  ⟦ Γ ⟧*₀ = Functor.F₀ (⟦ Γ ⟧*)

  ⟦_⟧*₁ : ∀ {n σ τ} (Γ : Vec Σ n) (arr : σ ⇒ τ) z s → Set ℓ
  ⟦ Γ ⟧*₁ = Functor.F₁ (⟦ Γ ⟧*)

  infix 10 _∋_⊨_

  data _∋_⊨_ {n} {Γ : Vec Σ n} : ∀ ω → ⟦ Γ ⟧*₀ ω → [ -, Γ ] → Set ℓ where

     ⊨⊤   : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω}
          → ω ∋ a ⊨ true

     ⊨∧   : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ₁ ϕ₂ : [ -, Γ ]}
          → ω ∋ a ⊨ ϕ₁ × ω ∋ a ⊨ ϕ₂
          → ω ∋ a ⊨ ϕ₁ ∧ ϕ₂
     ⊨∨   : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ₁ ϕ₂ : [ -, Γ ]}
          → ω ∋ a ⊨ ϕ₁ ⊎ ω ∋ a ⊨ ϕ₂
          → ω ∋ a ⊨ ϕ₁ ∨ ϕ₂

     ⊨∀   : ∀ {ω τ} {a : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, τ ∷ Γ ]}
          → (∀ b → ω ∋ (b , a) ⊨ ϕ)
          → ω ∋ a ⊨ ∀< τ > ϕ
     ⊨∃   : ∀ {ω τ} {a : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, τ ∷ Γ ]}
          → (∃[ b ] ω ∋ (b , a) ⊨ ϕ)
          → ω ∋ a ⊨ ∃< τ > ϕ

     ⊨∃◯  : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
          → map (λ { (σ , ρ) → ∃[ z ] ⟦ Γ ⟧*₁ ρ z a × σ ∋ z ⊨ ϕ }) (snd (arrows ω))
          → ω ∋ a ⊨ ∃◯ ϕ
     ⊨∀◯  : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
          → map (λ { (σ , ρ) → ∀ z → ⟦ Γ ⟧*₁ ρ z a → σ ∋ z ⊨ ϕ }) (snd (arrows ω))
          → ω ∋ a ⊨ ∀◯ ϕ

     ⊨U   : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ₁ ϕ₂ : [ -, Γ ]}
          → (p : Path ω)
          → (∃[ n ] (∀ i → i ≤ n → ∃[ zi ] let σ , ρ = comp p i in ⟦ Γ ⟧*₁ ρ zi a × σ ∋ zi ⊨ ϕ₁)
                  × (              ∃[ zn ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ zn a × σ ∋ zn ⊨ ϕ₂))
          → ω ∋ a ⊨ ϕ₁ U ϕ₂
     ⊨□   : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
          → (p : Path ω)
          → (∀ n  → ∃[ z ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ z a × σ ∋ z ⊨ ϕ)
          → ω ∋ a ⊨ □ ϕ
     ⊨◇   : ∀ {ω} {a : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
          → (p : Path ω)
          → (∃[ n ] ∃[ z ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ z a × σ ∋ z ⊨ ϕ)
          → ω ∋ a ⊨ ◇ ϕ

     ⊨≡   : ∀ {ω τ i} {a : ⟦ Γ ⟧*₀ ω} {t₁ t₂ : (n , Γ) ⊢ τ ⟨ i ⟩}
          → η (⟦ t₁ ⟧ᵗ) a ≡ η (⟦ t₂ ⟧ᵗ) a
          → ω ∋ a ⊨ (t₁ ≡ᵗ t₂)
     ⊨≢   : ∀ {ω τ i} {a : ⟦ Γ ⟧*₀ ω} {t₁ t₂ : (n , Γ) ⊢ τ ⟨ i ⟩}
          → η (⟦ t₁ ⟧ᵗ) a ≢ η (⟦ t₂ ⟧ᵗ) a
          → ω ∋ a ⊨ (t₁ ≢ᵗ t₂)
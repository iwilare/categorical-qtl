{-# OPTIONS --sized-types --allow-unsolved-metas #-}

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
open import CounterpartCategorial
open import TemporalStructure
open import DVec

module LTL {ℓ} {SΣ : Signature {ℓ}} (ℑ : CounterpartWModel SΣ) (T : TemporalStructure (CounterpartWModel.W ℑ)) where
  open CounterpartWModel ℑ
  open Signature SΣ
  open Terms SΣ hiding (_⊢_)
  open TemporalStructure.TemporalStructure T
  open RelPresheaf⇒
  open Category W

  data [_] : Ctx → Set ℓ where
    true : ∀ {Γ} → [ Γ ]
    _∧_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _∨_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _U_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    ◯_  : ∀ {Γ} → [ Γ ] → [ Γ ]
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
  infix 20 ◇_ □_ ◯_ _U_
  infix 23 ∃<_>_ ∀<_>_
  infix 25 _≡ᵗ_ _≢ᵗ_

  ⟦_⟧*₀ : ∀ {n} (Γ : Vec Σ n) ω → Set ℓ
  ⟦ Γ ⟧*₀ = Functor.F₀ (⟦ Γ ⟧*)

  ⟦_⟧*₁ : ∀ {n σ τ} (Γ : Vec Σ n) (arr : σ ⇒ τ) z s → Set ℓ
  ⟦ Γ ⟧*₁ = Functor.F₁ (⟦ Γ ⟧*)

  infix 10 _∋_⊨_

  data _∋_⊨_ {n} {Γ : Vec Σ n} : ∀ (ω : _) → ⟦ Γ ⟧*₀ ω → [ -, Γ ] → Set ℓ where
    ⊨⊤   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω}
         → ω ∋ s ⊨ true
    ⊨≡   : ∀ {ω τ i} {s : ⟦ Γ ⟧*₀ ω}
         → {t₁ t₂ : (n , Γ) ⊢ τ ⟨ i ⟩}
         → η (⟦ t₁ ⟧ᵗ) s ≡ η (⟦ t₂ ⟧ᵗ) s
         → ω ∋ s ⊨ (t₁ ≡ᵗ t₂)
    ⊨≢   : ∀ {ω τ i} {s : ⟦ Γ ⟧*₀ ω}
         → {t₁ t₂ : (n , Γ) ⊢ τ ⟨ i ⟩}
         → η (⟦ t₁ ⟧ᵗ) s ≢ η (⟦ t₂ ⟧ᵗ) s
         → ω ∋ s ⊨ (t₁ ≢ᵗ t₂)
    ⊨∧   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ₁ ϕ₂ : [ -, Γ ]}
         → ω ∋ s ⊨ ϕ₁ × ω ∋ s ⊨ ϕ₂
         → ω ∋ s ⊨ ϕ₁ ∧ ϕ₂
    ⊨∨   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ₁ ϕ₂ : [ -, Γ ]}
         → ω ∋ s ⊨ ϕ₁ ⊎ ω ∋ s ⊨ ϕ₂
         → ω ∋ s ⊨ ϕ₁ ∨ ϕ₂
    ⊨∀   : ∀ {ω τ} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, τ ∷ Γ ]}
         → (∀ b → ω ∋ (b , s) ⊨ ϕ)
         → ω ∋ s ⊨ ∀< τ > ϕ
    ⊨∃   : ∀ {ω τ} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, τ ∷ Γ ]}
         → (∃[ b ] ω ∋ (b , s) ⊨ ϕ)
         → ω ∋ s ⊨ ∃< τ > ϕ
    ⊨◯   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
         → map (λ { (σ , ρ) → ∃[ z ] ⟦ Γ ⟧*₁ ρ z s × σ ∋ z ⊨ ϕ }) (snd (arrows ω))
         → ω ∋ s ⊨ ◯ ϕ

    ⊨U   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ₁ ϕ₂ : [ -, Γ ]}
         → (p : Path ω)
         → (∃[ n ] (∀ i → i ≤ n → ∃[ zi ] let σ , ρ = comp p i in ⟦ Γ ⟧*₁ ρ zi s × σ ∋ zi ⊨ ϕ₁)
                 × (              ∃[ zn ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ zn s × σ ∋ zn ⊨ ϕ₂))
         → ω ∋ s ⊨ ϕ₁ U ϕ₂
    ⊨□   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
         → (p : Path ω)
         → (∀ n  → ∃[ z ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ z s × σ ∋ z ⊨ ϕ)
         → ω ∋ s ⊨ □ ϕ
    ⊨◇   : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
         → (p : Path ω)
         → (∃[ n ] ∃[ z ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ z s × σ ∋ z ⊨ ϕ)
         → ω ∋ s ⊨ ◇ ϕ

--    ---------------------------------------
--    ⊨∃CTL  : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
--        → ∃[ p ] {!   !}
--        → ω ∋ s ⊨ ◇ ϕ
--    ⊨∃□  : ∀ {ω} {s : ⟦ Γ ⟧*₀ ω} {ϕ : [ -, Γ ]}
--        → (p : Path ω)
--        → (∃[ n ] ∃[ z ] let σ , ρ = comp p n in ⟦ Γ ⟧*₁ ρ z s × σ ∋ z ⊨ ϕ)
--        → ω ∋ s ⊨ ◇ ϕ
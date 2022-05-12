{-# OPTIONS --sized-types #-}

open import Size
open import Level

open import Data.Nat     using (ℕ; _≤_)
open import Data.Product using (∃-syntax; _,_; -,_; _×_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Unit.Polymorphic renaming (⊤ to True)
open import Relation.Nullary using (¬_)

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
    ∃◯_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    ∀◯_ : ∀ {Γ} → [ Γ ] → [ Γ ]
    ∃C◯_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    ∀C◯_ : ∀ {Γ} → [ Γ ] → [ Γ ]
    ◇_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    □_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    neg : ∀ {Γ} → [ Γ ] → [ Γ ]
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
  infix 20 ◇_ □_ ∃◯_ ∀◯_ ∃C◯_ ∀C◯_ _U_
  infix 23 ∃<_>_ ∀<_>_
  infix 25 _≡ᵗ_ _≢ᵗ_

  ⟦_⟧*₀ : ∀ {n} (Γ : Vec Σ n) ω → Set ℓ
  ⟦ Γ ⟧*₀ = Functor.F₀ (⟦ Γ ⟧*)

  ⟦_⟧*₁ : ∀ {n σ τ} (Γ : Vec Σ n) (arr : σ ⇒ τ) z s → Set ℓ
  ⟦ Γ ⟧*₁ = Functor.F₁ (⟦ Γ ⟧*)

  infix 10 _∋_⊨_

  count : ∀ {n} {Γ : Vec Σ n} {ω σ} → ω ⇒ σ → ⟦ Γ ⟧*₀ ω → Set ℓ
  count ρ a = ∃[ z ] ⟦ _ ⟧*₁ ρ z a

  _∋_⊨_ : ∀ {n} {Γ : Vec Σ n} ω → ⟦ Γ ⟧*₀ ω → [ -, Γ ] → Set ℓ
  ω ∋ a ⊨ true = True
  ω ∋ a ⊨ ϕ₁ ∧ ϕ₂ = ω ∋ a ⊨ ϕ₁ × ω ∋ a ⊨ ϕ₂
  ω ∋ a ⊨ ϕ₁ ∨ ϕ₂ = ω ∋ a ⊨ ϕ₁ ⊎ ω ∋ a ⊨ ϕ₂
  ω ∋ a ⊨ ϕ₁ U ϕ₂ = ∀ (p : Path ω)
                  → (∃[ n ] (∀ i → i ≤ n → ∃[ zi ] let σ , ρ = comp p i in ⟦ _ ⟧*₁ ρ zi a × σ ∋ zi ⊨ ϕ₁)
                  × (                      ∃[ zn ] let σ , ρ = comp p n in ⟦ _ ⟧*₁ ρ zn a × σ ∋ zn ⊨ ϕ₂))
  ω ∋ a ⊨ ∃◯ ϕ = map (λ { (σ , ρ) → ∀ ((z , _) : count ρ a) → σ ∋ z ⊨ ϕ }) (snd (arrows ω))
  ω ∋ a ⊨ ∀◯ ϕ = map (λ { (σ , ρ) → ∀ z → ⟦ _ ⟧*₁ ρ z a → σ ∋ z ⊨ ϕ }) (snd (arrows ω))
  ω ∋ a ⊨ ∃C◯ ϕ = True
  ω ∋ a ⊨ ∀C◯ ϕ = True
  ω ∋ a ⊨ ◇ ϕ = ∀ (p : Path ω)
                   → (∃[ n ] ∃[ z ] let σ , ρ = comp p n in ⟦ _ ⟧*₁ ρ z a × σ ∋ z ⊨ ϕ)
  ω ∋ a ⊨ □ ϕ = ∀ (p : Path ω)
                   → (∀ n  → ∃[ z ] let σ , ρ = comp p n in ⟦ _ ⟧*₁ ρ z a × σ ∋ z ⊨ ϕ)
  ω ∋ a ⊨ ∃< τ > ϕ = (∃[ b ] ω ∋ (b , a) ⊨ ϕ)
  ω ∋ a ⊨ ∀< τ > ϕ = (∀ b → ω ∋ (b , a) ⊨ ϕ)
  ω ∋ a ⊨ t₁ ≡ᵗ t₂ = η (⟦ t₁ ⟧ᵗ) a ≡ η (⟦ t₂ ⟧ᵗ) a
  ω ∋ a ⊨ t₁ ≢ᵗ t₂ = η (⟦ t₁ ⟧ᵗ) a ≢ η (⟦ t₂ ⟧ᵗ) a
  ω ∋ a ⊨ neg ϕ = ¬ (ω ∋ a ⊨ ϕ)

{-# OPTIONS --sized-types #-}

open import Size
open import Level

open import Data.Vec as V using ([]; _∷_) renaming (Vec to Vector)

open import Data.Nat     using (ℕ; _≤_)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; -,_; _×_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     as V using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Unit.Polymorphic renaming (⊤ to True)
open import Data.Empty.Polymorphic renaming (⊥ to False)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Categories.Category
open import Categories.Functor

open import SortedAlgebra using (Signature; module Terms)
open import RelPresheaves
open import CounterpartCategorical
open import TemporalStructure
open import DVec
open import Utils

module LTL {ℓ} {SΣ : Signature {ℓ}} (ℑ : CounterpartWModel SΣ) (T : TemporalStructure (CounterpartWModel.W ℑ)) where
  open CounterpartWModel ℑ
  open Signature SΣ
  open Terms SΣ
  open TemporalStructure.TemporalStructure T
  open RelPresheaf⇒
  open Category W

  data [_] : Ctx → Set ℓ where
    true : ∀ {Γ} → [ Γ ]
    false : ∀ {Γ} → [ Γ ]
    !    : ∀ {Γ} → [ Γ ] → [ Γ ]
    _∧_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _∨_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
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
    ∃◯_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    ∀◯_  : ∀ {Γ} → [ Γ ] → [ Γ ]
    _∀U_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _∃U_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _∃W_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]
    _∀W_ : ∀ {Γ} → [ Γ ] → [ Γ ] → [ Γ ]

  ∃◇_ : ∀ {Γ} → [ Γ ] → [ Γ ]
  ∃◇ ϕ = true ∃U ϕ

  ∃□_ : ∀ {Γ} → [ Γ ] → [ Γ ]
  ∃□ ϕ = ϕ ∃W false

  ∀◇_ : ∀ {Γ} → [ Γ ] → [ Γ ]
  ∀◇ ϕ = true ∀U ϕ

  ∀□_ : ∀ {Γ} → [ Γ ] → [ Γ ]
  ∀□ ϕ = ϕ ∀W false

  infix 15 _∧_ _∨_
  infix 20 ∃◇_ ∃□_ ∀◇_ ∀□_ ∃◯_ ∀◯_ _∃U_ _∀U_ _∃W_ _∀W_
  infix 23 ∃<_>_ ∀<_>_
  infix 25 _≡ᵗ_ _≢ᵗ_

  ⟦_⟧*₀ : ∀ {n} (Γ : Vec Σ n) ω → Set ℓ
  ⟦ Γ ⟧*₀ = Functor.F₀ (⟦ Γ ⟧*)

  ⟦_⟧*₁ : ∀ {n σ τ} (Γ : Vec Σ n) (arr : σ ⇒ τ) z s → Set ℓ
  ⟦ Γ ⟧*₁ = Functor.F₁ (⟦ Γ ⟧*)

  ForAllArrows = λ {ω} {ℓ} (P : _ → Set ℓ) → map P (proj₂ (arrows ω))

  ClassicalAttribute : (X : RelPresheaf W) → Set (suc ℓ)
  ClassicalAttribute X = ∀ {ω} → (X.₀ ω → Set ℓ)
    where module X = Functor X

  X∃◯ : (X : RelPresheaf W) → ClassicalAttribute X → ClassicalAttribute X
  X∃◯ X A s = ForAllArrows λ { (σ , ρ) → ∃[ z ] X.₁ ρ z s × A s }
    where module X = Functor X

  X∀◯ : (X : RelPresheaf W) → ClassicalAttribute X → ClassicalAttribute X
  X∀◯ X A s = ForAllArrows λ { (σ , ρ) → ∀  z → X.₁ ρ z s → A s }
    where module X = Functor X

  X∃U : (X : RelPresheaf W) → ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  X∃U X A B {ω} s =
      ∀ (p : Path ω)
      → ∃[ n ] (∀ i → i ≤ n → ∃[ zᵢ ] X.₁ (proj₂ (comp p i)) zᵢ s × A zᵢ)
             × (              ∃[ zₙ ] X.₁ (proj₂ (comp p n)) zₙ s × B zₙ)
    where module X = Functor X

  X∀U : (X : RelPresheaf W) → ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  X∀U X A B {ω} s =
      ∀ (p : Path ω)
      → ∃[ n ] (∀ i → i ≤ n → ∀ zᵢ → X.₁ (proj₂ (comp p i)) zᵢ s → A zᵢ)
             × (              ∀ zₙ → X.₁ (proj₂ (comp p n)) zₙ s → B zₙ)
    where module X = Functor X

  X∃W : (X : RelPresheaf W) → ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  X∃W X A B {ω} s = X∃U X A B {ω} s
                  ⊎ (∀ (p : Path ω) → ∀ i → ∃[ zᵢ ] X.₁ (proj₂ (comp p i)) zᵢ s × A zᵢ)
    where module X = Functor X

  X∀W : (X : RelPresheaf W) → ClassicalAttribute X → ClassicalAttribute X → ClassicalAttribute X
  X∀W X A B {ω} s = X∀U X A B {ω} s
                  ⊎ (∀ (p : Path ω) → ∀ i → ∀ zᵢ → X.₁ (proj₂ (comp p i)) zᵢ s → A zᵢ)
    where module X = Functor X

  ⟨_⟩ : ∀ {n} {Γ : Vec Σ n} → [ -, Γ ] → ClassicalAttribute (⟦ Γ ⟧*)
  ⟨ true     ⟩ a = True
  ⟨ false    ⟩ a = False
  ⟨ ! ϕ      ⟩ a = ¬ ⟨ ϕ ⟩ a
  ⟨ ϕ₁ ∧ ϕ₂  ⟩ a = ⟨ ϕ₁ ⟩ a × ⟨ ϕ₂ ⟩ a
  ⟨ ϕ₁ ∨ ϕ₂  ⟩ a = ⟨ ϕ₁ ⟩ a ⊎ ⟨ ϕ₂ ⟩ a
  ⟨ ∃< τ > ϕ ⟩ a = ∃[ b ] ⟨ ϕ ⟩ (b , a)
  ⟨ ∀< τ > ϕ ⟩ a = ∀ b  → ⟨ ϕ ⟩ (b , a)
  ⟨ t₁ ≡ᵗ t₂ ⟩ a = η (⟦ t₁ ⟧ᵗ) a ≡ η (⟦ t₂ ⟧ᵗ) a
  ⟨ t₁ ≢ᵗ t₂ ⟩ a = η (⟦ t₁ ⟧ᵗ) a ≢ η (⟦ t₂ ⟧ᵗ) a
  ⟨ ∃◯ ϕ     ⟩ = X∃◯ (⟦ _ ⟧*) ⟨ ϕ ⟩
  ⟨ ∀◯ ϕ     ⟩ = X∀◯ (⟦ _ ⟧*) ⟨ ϕ ⟩
  ⟨ ϕ₁ ∃U ϕ₂ ⟩ = X∃U (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
  ⟨ ϕ₁ ∀U ϕ₂ ⟩ = X∀U (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
  ⟨ ϕ₁ ∃W ϕ₂ ⟩ = X∃W (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩
  ⟨ ϕ₁ ∀W ϕ₂ ⟩ = X∀W (⟦ _ ⟧*) ⟨ ϕ₁ ⟩ ⟨ ϕ₂ ⟩

  DecidableFormula : ∀ {n} {Γ : Vec Σ n} → [ -, Γ ] → Set ℓ
  DecidableFormula ϕ = ∀ ω (n : (⟦ _ ⟧*₀) ω) → Dec (⟨ ϕ ⟩ {ω} n)

{-

  infix 10 _∋_⊨_
  count : ∀ {n} {Γ : Vec Σ n} {ω σ} → ω ⇒ σ → ⟦ Γ ⟧*₀ ω → Set ℓ
  count ρ a = ∃[ z ] ⟦ _ ⟧*₁ ρ z a

  _∋_⊨_ : ∀ {n} {Γ : Vec Σ n} ω → ⟦ Γ ⟧*₀ ω → [ -, Γ ] → Set ℓ
  ω ∋ a ⊨ true = {!   !} --True
  ω ∋ a ⊨ ϕ₁ ∧ ϕ₂ = ω ∋ a ⊨ ϕ₁ × ω ∋ a ⊨ ϕ₂
  ω ∋ a ⊨ ϕ₁ ∨ ϕ₂ = ω ∋ a ⊨ ϕ₁ ⊎ ω ∋ a ⊨ ϕ₂
  ω ∋ a ⊨ ϕ₁ ∃U ϕ₂ = ∀ (p : Path ω)
                  → (∃[ n ] (∀ i → i ≤ n → ∃[ zi ] let σ , ρ = comp p i in ⟦ _ ⟧*₁ ρ zi a × σ ∋ zi ⊨ ϕ₁)
                  × (                      ∃[ zn ] let σ , ρ = comp p n in ⟦ _ ⟧*₁ ρ zn a × σ ∋ zn ⊨ ϕ₂))
  ω ∋ a ⊨ ∃◯ ϕ = map (λ { (σ , ρ) → Σ[ (z , _) ∈ count ρ a ] (∀ ((z , _) : count ρ a) → σ ∋ z ⊨ ϕ) }) (proj₂ (arrows ω))
  ω ∋ a ⊨ ∀◯ ϕ = map (λ { (σ , ρ) →                          (∀ ((z , _) : count ρ a) → σ ∋ z ⊨ ϕ) }) (proj₂ (arrows ω))
  ω ∋ a ⊨ ∃< τ > ϕ = (∃[ b ] ω ∋ (b , a) ⊨ ϕ)
  ω ∋ a ⊨ ∀< τ > ϕ = (∀ b → ω ∋ (b , a) ⊨ ϕ)
  ω ∋ a ⊨ t₁ ≡ᵗ t₂ = η (⟦ t₁ ⟧ᵗ) a ≡ η (⟦ t₂ ⟧ᵗ) a
  ω ∋ a ⊨ t₁ ≢ᵗ t₂ = η (⟦ t₁ ⟧ᵗ) a ≢ η (⟦ t₂ ⟧ᵗ) a
  ω ∋ a ⊨ ! ϕ = ¬ (ω ∋ a ⊨ ϕ)
-}

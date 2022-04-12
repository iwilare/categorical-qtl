{-# OPTIONS --sized-types #-}

open import Data.Vec        using (Vec; _∷_; [])
open import Data.Product    using (_,_; -,_)
open import Data.Unit.Base  using (tt)
open import Data.Fin        using (Fin; suc; zero)
open import Level           using (lift)
open import Function        using (_∘_; flip)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.PropositionalEquality as _≡_          using (_≡_; _≢_; refl)
open import Relation.Binary.PropositionalEquality.Properties      using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)

open import Categories.Category.Instance.Rels using (Rels)
open import Categories.Category

open import FreeCategory
open import DVec using (⊤)
open import SortedAlgebra
open import TemporalStructure
open import CounterpartAlgebraic
open import CounterpartCategorial
open import RelPresheaves
open import AlgebraicToCategorial

data ΣSort : Set where
  τ : ΣSort

data ΣFunction : Set where

Trivial : Signature
Trivial = record { Σ = ΣSort ; 𝓕 = ΣFunction ; sign = λ () }

data G₀-τ : Set where i : G₀-τ

G₀ : Σ-Algebra Trivial
G₀ = record { S = λ { τ → G₀-τ }
            ; F = λ ()
            }

data G₁-τ : Set where

G₁ : Σ-Algebra Trivial
G₁ = record { S = λ { τ → G₁-τ }
            ; F = λ ()
            }

data F₀-τ : G₀-τ → G₁-τ → Set where

F₀ : Σ-Homorel G₀ G₁
F₀ = record { ρ = λ { {τ} → F₀-τ }
            ; ρ-homo = λ ()
            }

data F₁-τ : G₁-τ → G₀-τ → Set where

F₁ : Σ-Homorel G₁ G₀
F₁ = record { ρ = λ { {τ} → F₁-τ }
            ; ρ-homo = λ ()
            }

data Obj : Set where
  s₀ s₁ : Obj

data _⇒_ : Obj → Obj → Set where
  f₀ : s₀ ⇒ s₁
  f₁ : s₁ ⇒ s₀

d : Obj → Σ-Algebra Trivial
d s₀ = G₀
d s₁ = G₁

𝑓₁ : ∀ {A B} → A ⇒ B → Σ-Homorel (d A) (d B)
𝑓₁ f₀ = F₀
𝑓₁ f₁ = F₁

data _⇝_[_] : (w₁ w₂ : Obj) → Σ-Homorel (d w₁) (d w₂) → Set where
  A₀ : s₀ ⇝ s₁ [ F₀ ]
  A₁ : s₁ ⇝ s₀ [ F₁ ]

𝔐 : CounterpartModel Trivial
𝔐 = record { W = Obj
           ; d = d
           ; _⇝_ = _⇒_
           ; Σ[_] = 𝑓₁
           }

ℑ : CounterpartWModel Trivial
ℑ = CategorifyModel 𝔐

open CounterpartWModel ℑ

T : TemporalStructure W
T = TStructure λ { s₀ → -, (-, f₀ *) ∷ []
                 ; s₁ → -, (-, f₁ *) ∷ []
                 }

----------------------------------------------------------------------------------------------------------------------------------------

import LTL

open LTL ℑ T

open SortedAlgebra.Terms Trivial

present : ∀ {τ} → [ -, τ ∷ [] ]
present {τ} = ∃< τ > # suc zero ≡ᵗ # zero

TrivialExistsTwoSteps : ∀ ω n → Dec (ω ∋ n , ⊤ ⊨ present {τ} ∧ ◯ (◯ present {τ}))
TrivialExistsTwoSteps s₀ i = no λ { (⊨∧ (⊨∃ (i , ⊨≡ refl) , ⊨◯ ())) }
TrivialExistsTwoSteps s₁ ()
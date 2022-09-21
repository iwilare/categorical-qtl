{-# OPTIONS --sized-types #-}

open import SortedAlgebra using (Signature; Σ-Algebra; Σ-Rel) 

module Counterpart.ClassicalToCategorical {ℓ} {Σ : Signature {ℓ}} where

import Data.Quiver.Paths

open import Categories.Functor  using (Functor)
open import Categories.Category using (_[_≈_])
open import Categories.Category using (Category)
open import Categories.Category.Construction.PathCategory using (PathCategory)
open import Categories.Category.Instance.Rels using (Rels)

open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (_,_)
open import Function using (id; flip)

open import Level using (lift)
open import Relation.Binary using (REL)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)

open import Counterpart.Categorical.TemporalModel
open import Counterpart.Categorical.TemporalStructure
open import Counterpart.Classical
open import RelPresheaves
open import VecT

ClassicalToCategorical : CounterpartModel Σ
                       → TemporalCounterpartWModel Σ
ClassicalToCategorical M =
  record
    { M = record
      { W = PathCategory
            record
              { Obj = W
              ; _⇒_ = _⇝_
              ; _≈_ = _≡_
              ; equiv = isEquivalence
              }
      ; ⟦_⟧ =
        λ τ →
          record
            { F₀ = λ ω → S (d ω) τ
            ; F₁ = StarRel
            ; identity     = (λ { refl → lift refl }) , λ { (lift refl) → refl }
            ; homomorphism = λ { {g = g} → star-homomorphism {f = g}}
            ; F-resp-≈     = star-resp-≈*
            }
      ; I =
        λ 𝑓 →
          record
            { η = λ {ω} → F (d ω) 𝑓
            ; imply = λ { {f = f} → star-imply f }
            }
      }
    ; T = TStructure
        λ { ε → ⊥
          ; (_ ◅ ε) → ⊤
          ; (_ ◅ (_ ◅ _)) → ⊥
          }
    }

  where
    open CounterpartModel M
    open Category (Rels ℓ ℓ) using (_≈_; _∘_)
    open Σ-Rel using (ρ; ρ-homo; op)
    open Σ-Algebra using (S; F)
    open RelPresheaves using (RelPresheaf)

    StarRel : ∀ {τ A B}
        → Star _⇝_ B A
        → REL (S (d A) τ) (S (d B) τ) ℓ
    StarRel ε = _≡_
    StarRel (B⇝C ◅ C⇝*A) = StarRel C⇝*A ; flip (ρ (f B⇝C))

    star-homomorphism : ∀ {τ X Y Z} {g : Star _⇝_ Y X} {f : Star _⇝_ Z Y}
        → StarRel {τ} (g ▻▻ f) ≈ StarRel {τ} f ∘ StarRel {τ} g
    star-homomorphism {f = ε} = (λ f → _ , f , refl)
                              , λ { (_ , f , refl) → f }
    star-homomorphism {f = x ◅ f} with star-homomorphism {f = f}
    ... | L⇒ , L⇐ = (λ { (J , g◅◅f , ρ) → let Y , Lf , Lg = L⇒ g◅◅f in Y , Lf , J , Lg , ρ })
                  , λ { (Y , Lf , J , Lg , ρ) → J , L⇐ (Y , Lf , Lg) , ρ }

    star-imply : ∀ {𝑓 σ τ t s} f
        → zip (StarRel f) t s
        → StarRel f (F (d τ) 𝑓 t) (F (d σ) 𝑓 s)
    star-imply ε       z = cong (F (d _) _) (zip-ext z)
    star-imply (_ ◅ m) x =
      let a , b , c = zip-rel-decomp x in
      F (d _) _ a , star-imply m b , ρ-homo (Σ-Rel.op (f _)) _ c

    open Data.Quiver.Paths.Paths (record { Obj = W ; _⇒_ = _⇝_ ; _≈_ = _≡_ ; equiv = isEquivalence }) using (_≈*_; ε; _◅_)

    ≡-chain : {A B : W} {f g : Star _⇝_ B A}
            → f ≈* g
            → f ≡ g
    ≡-chain ε = refl
    ≡-chain (x≈y ◅ x) = cong₂ _◅_ x≈y (≡-chain x)

    star-resp-≈* : ∀ {τ} {A B} {f g : Star _⇝_ B A}
        → f ≈* g
        → Rels ℓ ℓ [ StarRel {τ} f ≈ StarRel {τ} g ]
    star-resp-≈* f≈*g with ≡-chain f≈*g
    ... | refl = id , id

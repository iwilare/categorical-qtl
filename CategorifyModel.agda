{-# OPTIONS --sized-types #-}

open import Data.Vec        using (Vec; _∷_; [])
open import Data.Product    using (∃-syntax; _×_; _,_; -,_)
open import Level           using (lift)
open import Function        using (flip; id)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary.Construct.Composition                 using (_;_)
open import Relation.Binary.PropositionalEquality as _≡_          using (_≡_; refl; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties      using (isEquivalence)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)

open import Data.Quiver
open import Data.Quiver.Paths
open import Categories.Category.Construction.PathCategory

open import Categories.Category using (_[_≈_])
open import Categories.Functor using (Functor)
open Categories.Functor.Functor using (F₀; F₁; identity; homomorphism)

open import DVec
open import SortedAlgebra
open import TemporalStructure
open import CounterpartAlgebraic
open import CounterpartCategorical
open import RelPresheaves

open import Categories.Category using (Category)

CategorifyModel : ∀ {ℓ} {SΣ : Signature {ℓ}}
                → CounterpartModel SΣ
                → CounterpartWModel SΣ
CategorifyModel {ℓ} {SΣ} 𝔐 =
  record
    { W = PathCategory (record
            { Obj = W
            ; _⇒_ = _⇝_
            ; _≈_ = _≡_
            ; equiv = isEquivalence
            })
    ; ⟦_⟧ =
      λ τ →
        record
          { F₀ = λ ω → d₀ ω τ
          ; F₁ = StarRel
          ; identity = (λ { refl → lift refl }) , λ { (lift refl) → refl }
          ; homomorphism = λ { {g = g} → star-homomorphism g }
          ; F-resp-≈ = StarRel-resp-≈*
          }
    ; I =
      λ 𝑓 →
        record
          { η = d₁ _ 𝑓
          ; imply = λ { {f = f} → star-imply f }
          }
    } where open CounterpartModel 𝔐
            open import Categories.Category.Instance.Rels using (Rels)
            open Category (Rels ℓ ℓ)                      using (_≈_; _∘_)
            open Σ-Homorel                                using (ρ; ρ-homo; op)

            d₀ = λ ω → Σ-Algebra.S (d ω)
            d₁ = λ ω → Σ-Algebra.F (d ω)

            StarRel : ∀ {τ A B}
                → Star _⇝_ B A
                → REL (d₀ A τ) (d₀ B τ) ℓ
            StarRel ε = _≡_
            StarRel (B⇝C ◅ C⇝*A) = StarRel C⇝*A ; flip (ρ (Σ[ B⇝C ]))

            star-homomorphism : ∀ {τ X Y Z} {f : Star _⇝_ Y X} (g : Star _⇝_ Z Y)
                → StarRel {τ} (f ▻▻ g) ≈ StarRel {τ} g ∘ StarRel {τ} f
            star-homomorphism ε = (λ f → _ , f , refl)
                                , λ { (_ , f , refl) → f }
            star-homomorphism (x ◅ g) with star-homomorphism g
            ... | L⇒ , L⇐ = (λ { (J , g◅◅f , ρ) → let Y , Lf , Lg = L⇒ g◅◅f in Y , Lf , J , Lg , ρ })
                           , λ { (Y , Lf , J , Lg , ρ) → J , L⇐ (Y , Lf , Lg) , ρ }

            star-imply : ∀ {𝑓 σ τ t s} f
                → dzip (StarRel f) t s
                → StarRel f (d₁ τ 𝑓 t) (d₁ σ 𝑓 s)
            star-imply ε       z = cong (d₁ _ _) (dzip-ext z)
            star-imply (_ ◅ f) x =
              let a , b , c = dzip-rel-decomp x in
              d₁ _ _ a , star-imply f b , ρ-homo (Σ-Homorel.op (Σ[ _ ])) _ c

            open Paths (record { Obj = W ; _⇒_ = _⇝_ ; _≈_ = _≡_ ; equiv = isEquivalence }) using (_≈*_; ε; _◅_)

            ≡-chain : {A B : W} {f g : Star _⇝_ B A}
                    → f ≈* g
                    → f ≡ g
            ≡-chain ε = refl
            ≡-chain (x≈y ◅ x) = cong₂ _◅_ x≈y (≡-chain x)

            StarRel-resp-≈* : ∀ {τ} {A B} {f g : Star _⇝_ B A}
                    → f ≈* g
                    → Rels ℓ ℓ [ StarRel {τ} f ≈ StarRel {τ} g ]
            StarRel-resp-≈* f≈*g with ≡-chain f≈*g
            ... | refl = id , id

_* : ∀ {ℓ} {A : Set ℓ} {i j} {T : Rel A ℓ} → T i j → Star T i j
a * = a ◅ ε

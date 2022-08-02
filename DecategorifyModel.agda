{-# OPTIONS --sized-types #-}

open import Data.Vec        using (Vec; _∷_; [])
open import Data.Product    using (∃-syntax; _×_; _,_; -,_)
open import Level           using (lift)
open import Function        using (flip; id)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary.Construct.Composition                 using (_;_)
open import Relation.Binary.PropositionalEquality as _≡_          using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality.Properties      using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)

open import Categories.Functor using (Functor)
open Categories.Functor.Functor using (F₀; F₁; identity; homomorphism; F-resp-≈)

open import DVec
open import SortedAlgebra
open import TemporalStructure
open import CounterpartAlgebraic
open import CounterpartCategorical
open import RelPresheaves

open import Categories.Category using (Category)

DecategorifyModel : ∀ {ℓ} {SΣ : Signature {ℓ}}
                → CounterpartWModel SΣ
                → CounterpartModel SΣ
DecategorifyModel {ℓ} {SΣ} ℑ =
  record
    { W = W.Obj
    ; d = λ ω →
            record
              { S = λ Σ → Functor.₀ ⟦ Σ ⟧ ω
              ; F = λ 𝑓 → RelPresheaf⇒.η (I 𝑓)
              }
    ; _⇝_ = W._⇒_
    ; Σ[_] = λ x →
               record
                 { ρ = λ {τ} → flip (Functor.₁ ⟦ τ ⟧ x )
                 ; ρ-homo = λ f z → RelPresheaf⇒.imply (I f) (DVec.op z)
                 }
    } where open CounterpartWModel ℑ
            open Signature SΣ
            module W = Category W

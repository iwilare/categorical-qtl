{-# OPTIONS --sized-types #-}

open import Data.Vec        using (Vec; _∷_; [])
open import Data.Product    using (_,_; -,_)
open import Data.Unit.Base  using (tt)
open import Level           using (lift)
open import Function        using (flip; id)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Composition                 using (_;_)
open import Relation.Binary.PropositionalEquality as _≡_          using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties      using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)

open import DVec using (⊤)
open import SortedAlgebra
open import TemporalStructure
open import CounterpartAlgebraic
open import CounterpartCategorial
open import RelPresheaves
open import FreeCategory

open import Categories.Category using (Category)

postulate
  sorry : ∀ {ℓ} {A : Set ℓ} → A

CategorifyModel : ∀ {ℓ} {SΣ : Signature {ℓ}}
           → CounterpartModel SΣ
           → CounterpartWModel SΣ
CategorifyModel {ℓ} {SΣ} 𝔐 =
  record
    { W = FreeCategory W _⇝_
    ; ⟦_⟧ =
      λ τ →
        record
          { F₀ = λ ω → Σ-Algebra.S (d ω) τ
          ; F₁ = StarRel
          ; identity = (λ { refl → lift refl }) , λ { (lift refl) → refl }
          ; homomorphism = λ { {f = f} {g = g} → star-homomorphism {τ} {f = f} {g = g} }
          ; F-resp-≈ = λ { refl → id , id }
          }
    ; I =
      λ 𝑓 →
        record
          { η = Σ-Algebra.F (d _) 𝑓
          ; imply = λ { {f = f} → star-imply {𝑓} {f = f} }
          }
    } where open CounterpartModel 𝔐
            StarRel : ∀ {τ A B}
                    → Star _⇝_ B A
                    → Σ-Algebra.S (d A) τ
                    → Σ-Algebra.S (d B) τ
                    → Set ℓ
            StarRel ε = _≡_
            StarRel (B⇝C ◅ C⇝*A) = StarRel C⇝*A ; flip (Σ-Homorel.ρ (Σ[ B⇝C ]))

            open import Categories.Category.Instance.Rels
            open Category (Rels ℓ ℓ) using (_≈_; _∘_)

            star-homomorphism : ∀ {τ X Y Z} {f : Star _⇝_ Y X} {g : Star _⇝_ Z Y}
                     → StarRel {τ} (f ▻▻ g) ≈ StarRel {τ} g ∘ StarRel {τ} f
            star-homomorphism {g = ε} = (λ f → _ , f , refl)
                             , λ { (_ , f , refl) → f }
            star-homomorphism {g = x ◅ g} with star-homomorphism {g = g}
            ... | L⇒ , L⇐ = (λ { {x = x} (J , g◅◅f , ρ) → let Y , Lf , Lg = L⇒ g◅◅f in Y , Lf , J , Lg , ρ })
                           , λ { (Y , Lf , J , Lg , ρ) → J , L⇐ (Y , Lf , Lg) , ρ }

            star-imply : ∀ {𝑓} {σ τ : W}
                      {t : DVec.map (λ Σ → Σ-Algebra.S (d τ) Σ) (FunctionSignature.τ* (Signature.sign SΣ 𝑓))}
                      {s : DVec.map (λ Σ → Σ-Algebra.S (d σ) Σ) (FunctionSignature.τ* (Signature.sign SΣ 𝑓))}
                      {f : Star _⇝_ σ τ}
                  → DVec.dzip (StarRel f) t s
                  → StarRel f (Σ-Algebra.F (d τ) 𝑓 t) (Σ-Algebra.F (d σ) 𝑓 s)
            star-imply {𝑓} {t = t} {s = s} {f = ε} z     = sorry --with DVec.zipext {v = s} {v′ = t} z
            star-imply {𝑓} {t = t} {s = s} {f = p ◅ f} x = sorry
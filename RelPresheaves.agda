{-# OPTIONS --sized-types #-}

open import Categories.Category

module RelPresheaves {co cℓ ce} (C : Category co cℓ ce) where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)
open import Relation.Binary

import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Categories.Category.Cartesian
open import Categories.Category.Construction.Functors
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Rels
open import Categories.Functor hiding (id)
open import Categories.Functor.Properties
open import Categories.Functor.Presheaf

open import Function using (id; _∘_)
open import Data.Product
open import Data.Bool
open import Data.Unit.Polymorphic renaming (⊤ to Unit)
open import Utils

private
  variable
    o ℓ e : Level
    o′ ℓ′ : Level
    o″ ℓ″ : Level

RelPresheaf : Set (suc co ⊔ suc cℓ ⊔ ce)
RelPresheaf = Presheaf C (Rels co cℓ)

record RelPresheaf⇒ (X : RelPresheaf) (U : RelPresheaf) : Set (co ⊔ cℓ) where
  eta-equality
  private
    module X = Functor X
    module U = Functor U
  open Category C

  field
    η : ∀ {σ} → X.₀ σ → U.₀ σ
    imply : ∀ {σ τ t s} {f : C [ σ , τ ]}
            → X.₁ f    t     s
            → U.₁ f (η t) (η s)

RelPresheaves : Category _ _ _
RelPresheaves = record
  { Obj = RelPresheaf
  ; _⇒_ = RelPresheaf⇒
  ; _≈_ = λ F G →
          let module F = RelPresheaf⇒ F
              module G = RelPresheaf⇒ G in
              ∀ {σ} x → F.η {σ} x ≡ G.η {σ} x
  ; id = record { η     = id
                ; imply = id
                }
  ; _∘_ = λ F G →
          let module F = RelPresheaf⇒ F
              module G = RelPresheaf⇒ G in
              record { η     = F.η ∘ G.η
                     ; imply = F.imply ∘ G.imply
                     }
  ; assoc = λ f → refl
  ; sym-assoc = λ f → refl
  ; identityˡ = λ f → refl
  ; identityʳ = λ f → refl
  ; identity² = λ f → refl
  ; equiv = record
    { refl = λ f → refl
    ; sym = λ x≈y f → sym (x≈y f)
    ; trans = λ i≈j j≈k f → trans (i≈j f) (j≈k f)
    }
  ; ∘-resp-≈ = λ { {f = f} f≈h g≈i x → trans (cong (λ p → RelPresheaf⇒.η f p) (g≈i x)) (f≈h _) }
  }

module IsCartesian where

  RelPresheaves-Cartesian : Cartesian RelPresheaves
  RelPresheaves-Cartesian = record
    { terminal = record
      { ⊤ = record
        { F₀ = λ σ → Unit
        ; F₁ = λ f → λ { _ _ → Unit }
        ; identity = (λ { ⊤ → lift refl }) , (λ { (lift refl) → ⊤ })
        ; homomorphism = (λ { ⊤ → ⊤ , (⊤ , ⊤) }) , (λ { (⊤ , (⊤ , ⊤)) → ⊤ })
        ; F-resp-≈ = λ f → (λ { ⊤ → ⊤ }), (λ { ⊤ → ⊤ })
        }
      ; ⊤-is-terminal = record
        { ! = record { η = λ _ → ⊤ ; imply = λ _ → ⊤ }
        ; !-unique = λ f x → refl
        }
      }
    ; products = record
      { product = λ {A B} →
        let module A = Functor A
            module B = Functor B
        in record
        { A×B = record
          { F₀ = λ σ → A.₀ σ × B.₀ σ
          ; F₁ = λ f → λ { (a , b) (c , d) → A.₁ f a c × B.₁ f b d }
          ; identity =
              (λ { {_ , _} {_ , _} (f , g) →
                lift (cong₂ _,_ (lower (proj₁ A.identity f))
                                (lower (proj₁ B.identity g))) })
            , (λ { (lift refl) →
                  proj₂ A.identity (lift refl)
                , proj₂ B.identity (lift refl) })
          ; homomorphism =
              (λ { (a , b) → let (af , ag , ah) = proj₁ A.homomorphism a
                                 (bf , bg , bh) = proj₁ B.homomorphism b
                              in (af , bf) , (ag , bg) , (ah , bh) })
            , (λ { ((af , bf) , (ag , bg) , (ah , bh)) →
                   proj₂ A.homomorphism (af , ag , ah)
                 , proj₂ B.homomorphism (bf , bg , bh)})
          ; F-resp-≈ =
            λ { e → let (fr1 , fr2) = A.F-resp-≈ e
                        (gr1 , gr2) = B.F-resp-≈ e
                     in (λ { (x , y) → fr1 x , gr1 y })
                      , (λ { (x , y) → fr2 x , gr2 y }) }
          }
        ; π₁ = record { η = proj₁ ; imply = proj₁ }
        ; π₂ = record { η = proj₂ ; imply = proj₂ }
        ; ⟨_,_⟩ = λ {F} α β →
            let module F = Functor F
                module α = RelPresheaf⇒ α
                module β = RelPresheaf⇒ β in
                record { η     = < α.η     , β.η     >
                       ; imply = < α.imply , β.imply >
                       }
        ; project₁ = λ f → refl
        ; project₂ = λ f → refl
        ; unique = λ p₁ p₂ x → sym (cong₂ _,_ (p₁ x) (p₂ x))
        }
      }
    }

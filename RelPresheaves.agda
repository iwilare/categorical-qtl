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

import Categories.Category.Monoidal.Instance.Rels as T
import Categories.Category.Construction.Properties.Presheaves.Cartesian as K

open import Function using (id; _∘_)
open import Data.Product
open import Data.Bool
open import Data.Unit.Polymorphic hiding (tt)
open import Data.Unit.Base using (tt)

private
  variable
    ℓ : Level
    o′ ℓ′ : Level
    o″ ℓ″ : Level

RelPresheaf : Set _
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

⟨_,_⟩ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {a b : A} {c d : B} → a ≡ b → c ≡ d → (a , c) ≡ (b , d)
⟨ refl , refl ⟩ = refl

RelPresheaves : Category (suc co ⊔ suc cℓ ⊔ ce) (co ⊔ cℓ) co
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

RelPresheaf⊤ : Presheaf C (Rels o′ ℓ′)
RelPresheaf⊤ = record
  { F₀ = λ σ → ⊤
  ; F₁ = λ f → λ { _ _ → ⊤ }
  ; identity = (λ { (lift tt) → lift refl }) , (λ { (lift refl) → lift tt })
  ; homomorphism = (λ (lift tt) → (lift tt) , ((lift tt) , (lift tt)))
                 , (λ { (lift tt , (lift tt , lift tt)) → lift tt })
  ; F-resp-≈ = λ f → (λ { (lift tt) → lift tt }), (λ { (lift tt) → lift tt })
  }

RelPresheaves× : (A : Presheaf C (Rels o′ ℓ′)) → (B : Presheaf C (Rels o″ ℓ″)) → Presheaf C (Rels (o′ ⊔ o″) (ℓ′ ⊔ ℓ″))
RelPresheaves× A B = record
  { F₀           = λ σ → A.₀ σ × B.₀ σ
  ; F₁           = λ f → λ { (a , b) (c , d) → A.₁ f a c × B.₁ f b d }
  ; identity     = (λ { (e , f) → lift (⟨ lower (proj₁ A.identity e) , lower (proj₁ B.identity f) ⟩) })
                 , (λ { (lift refl) → proj₂ A.identity (lift refl) , proj₂ B.identity (lift refl) })
  ; homomorphism = (λ { (a , b) →
                      let (af , ag , ah) = proj₁ A.homomorphism a
                          (bf , bg , bh) = proj₁ B.homomorphism b
                        in (af , bf) , (ag , bg) , (ah , bh) })
                 , (λ { ((af , bf) , (ag , bg) , (ah , bh)) →
                        proj₂ A.homomorphism (af , ag , ah)
                      , proj₂ B.homomorphism (bf , bg , bh)})
  ; F-resp-≈     = λ { e →
                       let (fr1 , fr2) = A.F-resp-≈ e
                           (gr1 , gr2) = B.F-resp-≈ e
                        in (λ { (x , y) → fr1 x , gr1 y })
                         , (λ { (x , y) → fr2 x , gr2 y }) }
  } where module A = Functor A
          module B = Functor B

module IsCartesian where

  RelPresheaves-Cartesian : Cartesian RelPresheaves
  RelPresheaves-Cartesian = record
    { terminal = record
      { ⊤ = RelPresheaf⊤
      ; ⊤-is-terminal = record
        { !        = record { η = λ _ → lift tt ; imply = λ _ → lift tt }
        ; !-unique = λ f x → refl
        }
      }
    ; products = record
      { product = λ {A B} →
        let module A = Functor A
            module B = Functor B
        in record
        { A×B = RelPresheaves× A B
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

{-
P[_] : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
P[_] {ℓ} X = X → Set ℓ

PowerRel : ∀ {ℓ} {A B : Set ℓ} → REL A B ℓ → REL (P[ A ]) (P[ B ]) ℓ
PowerRel R S′ S = ∀ a → S′ a → ∃[ b ] (S b × R a b)

MyPowerRel : ∀ {ℓ} {A B : Set ℓ} → REL A B ℓ → REL (P[ A ]) (P[ B ]) ℓ
MyPowerRel R S′ S = ∀ {a b} → S′ a → S b → R a b

PX : ∀ {o ℓ} (X : Presheaf C (Rels o ℓ)) → Presheaf C (Rels (suc o) (suc ℓ))
PX {o} {ℓ} X = record
  { F₀ = λ σ → P[ X.₀ σ ]
  ; F₁ = λ f → λ S S′ → ∀ {a b} → S a → S′ b → Lift _ (X.₁ f a b)
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  } where module X = Functor X

∈X : ∀ {o′ ℓ′} → (X : Presheaf C (Rels o′ ℓ′)) → Presheaf C (Rels {!   !} {!   !})
∈X X = record
    { F₀ = λ σ → Σ[ (a , A) ∈ (X.₀ σ × P[ X.₀ σ ]) ] A a
    ; F₁ = λ f → λ ((a , A) , a∈A) ((b , B) , b∈B) → Lift _ (X.₁ f a b × {!   !}) --λ σ ω → {!   !}
    ; identity = {!   !}
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !}
    } where module X = Functor X
-}
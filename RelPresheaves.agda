open import Categories.Category

module RelPresheaves {co cℓ ce} (C : Category co cℓ ce) where

open import Level
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function.Equality using (Π) renaming (_∘_ to _∙_)
open import Relation.Binary

open import Categories.Category.Cartesian
open import Categories.Category.Construction.Functors
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Rels
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation

import Categories.Category.Monoidal.Instance.Rels as T
import Categories.Category.Construction.Properties.Presheaves.Cartesian as K

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Unit.Polymorphic hiding (tt)
open import Data.Unit.Base using (tt)

open import Utils

private
  variable
    ℓ : Level
    o′ ℓ′ : Level
    o″ ℓ″ : Level

RelPresheaf : ∀ {o ℓ e} (C : Category o ℓ e) → Set _
RelPresheaf {o} {ℓ} C = Presheaf C (Rels o ℓ)

RelPresheaves : ∀ o′ ℓ′ {o ℓ e} → Category o ℓ e → Category _ _ _
RelPresheaves o′ ℓ′ C = Functors (Category.op C) (Rels o′ ℓ′)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

RelPresheaf⊤ : Presheaf C (Rels o′ ℓ′)
RelPresheaf⊤ = record
  { F₀ = λ x → ⊤
  ; F₁ = λ { f _ _ → ⊤ }
  ; identity = (λ { (lift tt) → lift refl }) , (λ { (lift refl) → lift tt })
  ; homomorphism = (λ (lift tt) → (lift tt) , ((lift tt) , (lift tt)))
                 , (λ { (lift tt , (lift tt , lift tt)) → lift tt })
  ; F-resp-≈ = λ f → (λ { (lift tt) → lift tt }), (λ { (lift tt) → lift tt })
  }

RelPresheaves× : (A : Presheaf C (Rels o′ ℓ′)) → (B : Presheaf C (Rels o″ ℓ″)) → Presheaf C (Rels (o′ ⊔ o″) (ℓ′ ⊔ ℓ″))
RelPresheaves× A B = record
  { F₀           = λ X → A.₀ X × B.₀ X
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

P[_] : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
P[_] {ℓ} X = X → Set ℓ

PowerRel : ∀ {A B : Set ℓ} → (R : REL A B ℓ) → REL (P[ A ]) (P[ B ]) ℓ --Presheaf C (Rels _ (suc ℓ ⊔ o′ ⊔ ℓ′))
PowerRel R S′ S = ∀ a → S′ a → ∃[ b ] (S b × R a b)





PX : (X : Presheaf C (Rels o′ ℓ′)) → Presheaf C (Rels {!   !} {!   !})
PX X = record
  { F₀ = λ σ →  P[ X.₀ σ ]
  ; F₁ = λ f → {! PowerRel ?  !} --PowerRel (X.₁ f)
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  } where module X = Functor X


{-
∈X : ∀ {o′ ℓ′} → (X : Presheaf C (Rels o′ ℓ′)) → Presheaf C (Rels _ (suc ℓ ⊔ o′ ⊔ ℓ′))
∈X X = record
    { F₀ = λ σ → Σ[ (a , A) ∈ (X.₀ σ × P[ X.₀ σ ]) ] A a
    ; F₁ = λ f → λ ((a , A) , a∈A) ((b , B) , b∈B) → Lift _ (X.₁ f a b × {!   !}) --λ σ ω → {!   !}
    ; identity = {!   !}
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !}
    } where module X = Functor X

{-
-}

{-
module IsCartesian o′ ℓ′ where

  private
    module C = Category C
    module P = Category (RelPresheaves o′ ℓ′ C)
    module R = Category (Rels o′ ℓ′)
    open R

  RelPresheaves-Cartesian : Cartesian (RelPresheaves o′ ℓ′ C)
  RelPresheaves-Cartesian = record
    { terminal = record
      { ⊤ = RelPresheaf⊤
      ; ⊤-is-terminal = record
        { !        = ntHelper (record { η = λ { X x (lift tt) → {!   !} } ; commute = {!   !} })
        ; !-unique = {!   !} --λ f → (λ x₁ → {!  !}) , {!   !}
        }
      }
      ; products = record
        { product = λ {A B} →
          let module A = Functor A
              module B = Functor B
          in record
          { A×B = RelPresheaves× A B
          ; π₁ = ntHelper record
            { η = λ { σ (a , b) a′ → Lift ℓ′ (a ≡ a′) }
            ; commute = _
            }
          ; π₂ = ntHelper record
            { η = λ { σ (a , b) b′ → Lift ℓ′ (b ≡ b′) }
            ; commute = _
            }
          ; ⟨_,_⟩ = λ {F} α β →
            let module F = Functor F
                module α = NaturalTransformation α
                module β = NaturalTransformation β
            in ntHelper record
            { η       = λ { σ Fσ (Aσ , Bσ) → α.η σ Fσ Aσ × β.η σ Fσ Bσ }
            ; commute = {!   !} --λ f →
                        --  let (αf₁ , αf₂) = α.commute f
                        --      (βf₁ , βf₂) = β.commute f in
                        --       (λ { (a , b , (c , d)) →
                        --         let (α1 , α2 , α3) = αf₁ (a , b , c)
                        --             (β1 , β2 , β3) = βf₁ (a , b , d)
                        --         in (α1 , β1) , (α2 , β2) , (α3 , β3)})
                        --     , (λ { ((α1 , β1) , (α2 , β2) , (α3 , β3)) →
                        --         let (a1 , a2 , a3) = αf₂ ({!   !} , {!   !} , {!   !})
                        --             (b1 , b2 , b3) = βf₂ ({!   !} , {!   !} , {!   !})
                        --          in b1 , b2 , {!   !} , {!   !} })
            }
          ; project₁ = {!   !} --(λ { ((a , b) , (c , d) , lift refl) → c }) , (λ { {F} {σ} a → {!   !} })
          ; project₂ = {!   !}
          ; unique = {!   !}
          }
        }
      }                       -- cerchio

  --record
  --  { terminal = record
  --    { ⊤        = record
  --      { F₀           = λ x → record
  --        { Carrier       = Lift o′ ⊤
  --        ; _≈_           = λ _ _ → Lift ℓ′ ⊤
  --        ; isEquivalence = _
  --        }
  --      }
  --    ; ⊤-is-terminal = record
  --      { !        = _
  --      ; !-unique = _
  --      }
  --    }
  --  ; products = record
  --    { product = λ {A B} →
  --      let module A = Functor A
  --          module B = Functor B
  --      in record
  --      { A×B      = Presheaves× A B
  --      ; π₁       = ntHelper record
  --        { η       = λ X → record
  --          { _⟨$⟩_ = λ { (fst , _) → fst }
  --          ; cong  = λ { (eq , _)  → eq }
  --          }
  --        ; commute = λ { f (eq , _) → Π.cong (A.F₁ f) eq }
  --        }
  --      ; π₂       = ntHelper record
  --        { η       = λ X → record
  --          { _⟨$⟩_ = λ { (_ , snd) → snd }
  --          ; cong  = λ { (_ , eq)  → eq }
  --          }
  --        ; commute = λ { f (_ , eq) → Π.cong (B.F₁ f) eq }
  --        }
  --      ; ⟨_,_⟩    = λ {F} α β →
  --        let module F = Functor F
  --            module α = NaturalTransformation α
  --            module β = NaturalTransformation β
  --        in ntHelper record
  --        { η       = λ Y → record
  --          { _⟨$⟩_ = λ R → α.η Y ⟨$⟩ R , β.η Y ⟨$⟩ R
  --          ; cong  = λ eq → Π.cong (α.η Y) eq , Π.cong (β.η Y) eq
  --          }
  --        ; commute = λ f eq → α.commute f eq , β.commute f eq
  --        }
  --      ; project₁ = λ {F α β x} eq →
  --        let module F = Functor F
  --            module α = NaturalTransformation α
  --            module β = NaturalTransformation β
  --        in Π.cong (α.η x) eq
  --      ; project₂ = λ {F α β x} eq →
  --        let module F = Functor F
  --            module α = NaturalTransformation α
  --            module β = NaturalTransformation β
  --        in Π.cong (β.η x) eq
  --      ; unique   = λ {F α β δ} eq₁ eq₂ {x} eq →
  --        let module F = Functor F
  --            module α = NaturalTransformation α
  --            module β = NaturalTransformation β
  --            module δ = NaturalTransformation δ
  --        in Setoid.sym (A.₀ x) (eq₁ (Setoid.sym (F.₀ x) eq))
  --         , Setoid.sym (B.₀ x) (eq₂ (Setoid.sym (F.₀ x) eq))
  --      }
  --    }
  --  }

  module RelPresheaves-Cartesian = Cartesian RelPresheaves-Cartesian
-}
-}
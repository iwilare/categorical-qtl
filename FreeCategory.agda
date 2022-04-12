{-# OPTIONS --sized-types #-}

open import Data.Vec                                         using (Vec; [_]; _∷_; [])
open import Data.Product                                     using (_,_; -,_)
open import Data.Unit.Base                                   using (tt)
open import Level                                            using (lift)
open import Relation.Binary                                  using (Rel; Reflexive; Trans)
open import Relation.Binary.PropositionalEquality as _≡_     using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)

open import Categories.Category

FreeCategory : ∀ {ℓ} → (Obj : Set ℓ) → Rel Obj ℓ → Category _ _ _
FreeCategory Obj _⇒_ = record
  { Obj = Obj
  ; _⇒_ = Star _⇒_
  ; _≈_ = _≡_
  ; id  = ε
  ; _∘_ = _▻▻_
  ; assoc = λ { {f = f} {g = g} {h = h} → assoc {f = f} {g = g} {h = h} }
  ; sym-assoc = λ { {f = f} {g = g} {h = h} → _≡_.sym (assoc {f = f} {g = g} {h = h}) }
  ; identityˡ = identityˡ
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = _≡_.isEquivalence
  ; ∘-resp-≈ = λ { refl refl → refl }
  } where
    assoc : ∀ {A B C D : Obj} {f : Star _⇒_ A B} {g : Star _⇒_ B C} {h : Star _⇒_ C D}
          → f ◅◅ (g ◅◅ h) ≡ (f ◅◅ g) ◅◅ h
    assoc {f = ε}                                                           = refl
    assoc {f = _ ◅ f} {g = g} {h = h} rewrite assoc {f = f} {g = g} {h = h} = refl

    identityˡ : ∀ {A B : Obj} {f : Star _⇒_ A B}
             → f ◅◅ ε ≡ f
    identityˡ {f = ε}                               = refl
    identityˡ {f = _ ◅ f} rewrite identityˡ {f = f} = refl

_* : ∀ {ℓ} {A : Set ℓ} {i j} {T : Rel A ℓ} → T i j → Star T i j
a * = a ◅ ε
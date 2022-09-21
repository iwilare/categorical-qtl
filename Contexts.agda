{-# OPTIONS --sized-types #-}

module Contexts {ℓ} where

open import Categories.Category
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.Vec.Membership.Propositional using (_∈_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Level
open import Function using (_∘_) renaming (id to idᶠ)
open import Relation.Binary.HeterogeneousEquality using (≅-to-≡)
open import Data.Fin using (Fin)
open import Size using (∞)

open import SortedAlgebra using (Signature)
open import VecT

Contexts : Signature {ℓ} → Category _ _ ℓ
Contexts Σ =
  record
    { Obj = ∃[ n ] Ctx n
    ; _⇒_ = _⇒_
    ; _≈_ = λ f g → ∀ {x} → f x ≡ g x
    ; id = id
    ; _∘_ = λ f g → sub f ∘ g
    ; assoc = λ { {f = f} → assoc (f _) }
    ; sym-assoc = λ { {f = f} → sym (assoc (f _)) }
    ; identityˡ = λ { {f = f} {x} → identityˡ (f x) }
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = Eq.refl
                     ; sym =  λ x → Eq.sym x
                     ; trans = λ e e′ → Eq.trans e e′
                     }
    ; ∘-resp-≈ = λ { {i = i} e e′ → trans (cong (sub _) e′) (sub-resp-≈ (i _) e) }
    } where
        open SortedAlgebra.Term Σ using (Subst; Ctx; _⊢_⟨_⟩; sub; var; fun; id)

        _⇒_ = λ x y → Subst (proj₂ x) (proj₂ y)

        assoc : ∀ {i τ A B C} {f : A ⇒ B} {g : B ⇒ C} (x : proj₂ A ⊢ τ ⟨ i ⟩)
              → sub (sub g ∘ f) x ≡ sub g (sub f x)
        assoc (var _)   = refl
        assoc (fun f x) = cong (fun f) (trans (map-cong assoc) map-comp)

        identityˡ : ∀ {τ i} {A : ∃[ n ] Ctx n} (x : proj₂ A ⊢ τ ⟨ i ⟩)
                  → sub var x ≡ idᶠ x
        identityˡ (var _) = refl
        identityˡ (fun f x) = cong (fun f) (trans (map-cong identityˡ) map-id)

        sub-resp-≈ : ∀ {i τ A B} {f g : A ⇒ B} (x : proj₂ A ⊢ τ ⟨ i ⟩)
                   → (∀ {x} → f x ≡ g x)
                   → sub f x ≡ sub g x
        sub-resp-≈ (var _) f≈g = f≈g
        sub-resp-≈ (fun f x) f≈g = cong (fun f) (map-cong λ σ → sub-resp-≈ σ f≈g)

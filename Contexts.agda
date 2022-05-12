{-# OPTIONS --sized-types #-}

open import Categories.Category
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Vec.Membership.Propositional using (_∈_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Level
open import Function using (_∘_) renaming (id to idᶠ)
open import Relation.Binary.HeterogeneousEquality using (≅-to-≡)
open import Data.Fin using (Fin)

open import SortedAlgebra using (Signature)
open import DVec

Con : ∀ {ℓ} → Signature {ℓ} → Category _ _ ℓ
Con {ℓ} SΣ =
  record
    { Obj = Ctx
    ; _⇒_ = Subst
    ; _≈_ = λ f g → ∀ {x} → f x ≡ g x
    ; id = id
    ; _∘_ = λ f g → sub f ∘ g
    ; assoc = λ { {f = f} →  assoc (f _) }
    ; sym-assoc = λ { {f = f} → sym (assoc (f _)) }
    ; identityˡ = λ { {f = f} → identityˡ  (f _) }
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = Eq.refl
                     ; sym =  λ x → Eq.sym x
                     ; trans = λ e e′ → Eq.trans e e′
                     }
    ; ∘-resp-≈ = λ { {i = i} e e′ → trans (cong (sub _) e′) (sub-resp-≈ (i _) e) }
    } where
        open SortedAlgebra.Terms SΣ using (Subst; Ctx; _⊢_⟨_⟩; sub; var; fun; id)

        assoc : ∀ {i τ A B C} {f : Subst A B} {g : Subst B C} (x : A ⊢ τ ⟨ i ⟩)
              → sub (sub g ∘ f) x ≡ sub g (sub f x)
        assoc (var _)   = refl
        assoc (fun f x) = cong (fun f) (trans (dmap-cong assoc) dmap-comp)

        identityʳ : ∀ {i τ A} (x : A ⊢ τ ⟨ i ⟩)
                  → sub var x ≡ idᶠ x
        identityʳ (var _) = refl
        identityʳ (fun f x) = cong (fun f) (trans (dmap-cong identityʳ) dmap-id)

        identityˡ : ∀ {i τ A} (x : A ⊢ τ ⟨ i ⟩)
                  → sub var x ≡ idᶠ x
        identityˡ (var _) = refl
        identityˡ (fun f x) = cong (fun f) (trans (dmap-cong identityˡ) dmap-id)

        sub-resp-≈ : ∀ {i τ A B} {f g : Subst A B} (x : A ⊢ τ ⟨ i ⟩)
                   → (∀ {x} → f x ≡ g x)
                   → sub f x ≡ sub g x
        sub-resp-≈ (var _) f≈g = f≈g
        sub-resp-≈ (fun f x) f≈g = cong (fun f) (dmap-cong λ σ → sub-resp-≈ σ f≈g)
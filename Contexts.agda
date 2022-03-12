{-# OPTIONS --sized-types #-}

open import Categories.Category
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import SortedAlgebra
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional using (Extensionality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Level

open import DVec

private
  variable
    ℓ : Level

postulate
   Ext : Extensionality ℓ ℓ

Con : Signature → Category _ _ _
Con SΣ =
  record
    { Obj = Ctx
    ; _⇒_ = Ctx⇒
    ; _≈_ = _≡_
    ; id = CtxId
    ; _∘_ = _∘_
    ; assoc = λ {A B C D f g h} → Ext λ x → assoc (h x)
    ; sym-assoc = λ {A B C D f g h} → Ext λ x → sym (assoc (h x))
    ; identityˡ = refl
    ; identityʳ = λ {A B f} → Ext λ e →
           begin
              sub (CtxId ᵀ) (f e) ≡⟨ cong (λ p →  sub (λ {r} → {!   !}) _ ) (idᵣ {A})  ⟩
              sub (SubstId {A}) (f e) ≡⟨ subid (f e) ⟩
                                (f e) ∎
            --  trans (cong (λ (p : ) → sub p (f e)) (idᵣ f)) (subid (f e))
    ; identity² = refl
    ; equiv = isEquivalence
    ; ∘-resp-≈ = λ { refl refl → refl }
    } where
        open SortedAlgebra.Terms SΣ

        Ctx⇒ : Ctx → Ctx → Set
        Ctx⇒ Γ (_ , Γ′) = dmap (λ τ → Γ ⊢ τ) Γ′

        _≈_ : ∀ {Γ Δ} → Ctx⇒ Δ Γ → Ctx⇒ Δ Γ → Set
        (f ≈ g) = ∀ i → f i ≡ g i

        _ᵀ : ∀ {Γ Δ} → Ctx⇒ Δ Γ → Subst Γ Δ
        (g ᵀ) (V i) = g i

        _∘_ : {A B C : Ctx} → Ctx⇒ B C → Ctx⇒ A B → Ctx⇒ A C
        f ∘ g = map (sub (g ᵀ)) f

        CtxId : ∀ {Γ} → Ctx⇒ Γ Γ
        CtxId i = var (V i)

        SubstId : ∀ {Γ} → Subst Γ Γ
        SubstId (V i) = var (V i)

        idᵣ : ∀ {Γ A} → (CtxId {Γ}) ᵀ ≡ SubstId {Γ}
        idᵣ {Γ} {A} = Ext aid
           where aid : (x : Γ ∋ A) → (CtxId {Γ} ᵀ) x ≡ SubstId {Γ} x
                 aid (V _) = refl

        subid : ∀ {Γ A i} (x : Γ ⊢ A ⟦ i ⟧) → sub SubstId x ≡ x
        subid (var (V i)) = refl
        subid (fun f x) = cong (fun f) (Ext λ i → subid (x i))

        assoc : ∀ {i τ} {A B C : Ctx} {f : Ctx⇒ A B} {g : Ctx⇒ B C} (x : C ⊢ τ ⟦ i ⟧)
              → sub (f ᵀ) (sub (g ᵀ) x) ≡ sub ((λ x → sub (f ᵀ) (g x)) ᵀ) x
        assoc (var (V _)) = refl
        assoc (fun f x) = cong (fun f) (Ext λ i → assoc (x i))
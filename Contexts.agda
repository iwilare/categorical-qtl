{-# OPTIONS --sized-types #-}

open import Categories.Category
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional using (Extensionality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Level
open import Relation.Binary.HeterogeneousEquality using (≅-to-≡)

open import SortedAlgebra
open import DVec            as D
open import DVec.Functional as F

open import Data.Vec using (Vec; _∷_; [])

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
    ; _≈_ = _≈_
    ; id = CtxId
    ; _∘_ = _∘_
    ; assoc = λ { {h = h} i → assoc (h i) }
    ; sym-assoc = λ { {h = h} i → sym (assoc (h i)) }
    ; identityˡ = λ i → refl --refl
    ; identityʳ = {!   !}
-- λ {A B f} → Ext λ e →
--         begin
--            sub (CtxId ᵀ) (f e) ≡⟨ cong (λ p →  sub (λ {r} → {!   !}) _ ) (idᵣ {A})  ⟩
--           sub (SubstId {A}) (f e) ≡⟨ subid (f e) ⟩
--                              (f e) ∎
--          --  trans (cong (λ (p : ) → sub p (f e)) (idᵣ f)) (subid (f e))
    ; identity² = λ i → refl
    ; equiv = record { refl = λ i → refl
                     ; sym = λ v i → Eq.sym (v i)
                     ; trans = λ v v′ i → Eq.trans (v i) (v′ i)
                     }
    ; ∘-resp-≈ = λ { a b i → {!   !} } --λ { refl refl → refl }
    } where
        open SortedAlgebra.Terms SΣ

        Ctx⇒ : Ctx → Ctx → Set
        Ctx⇒ Γ (_ , Γ′) = F.map (λ τ → Γ ⊢ τ) Γ′

        _≈_ : ∀ {Γ Δ} → Ctx⇒ Δ Γ → Ctx⇒ Δ Γ → Set
        (f ≈ g) = ∀ i → f i ≡ g i

        _≈ₛ_ : ∀ {Γ Δ} → Subst Δ Γ → Subst Δ Γ → Set
        (f ≈ₛ g) = ∀ {A} (s : _ ∋ A) → f s ≡ g s

        infixl 15 _≈_ _≈ₛ_

        _ᵀ : ∀ {Γ Δ} → Ctx⇒ Δ Γ → Subst Γ Δ
        (g ᵀ) (V i) = g i

        _∘_ : {A B C : Ctx} → Ctx⇒ B C → Ctx⇒ A B → Ctx⇒ A C
        f ∘ g = F.dmapAssoc (sub (g ᵀ)) f

        CtxId : ∀ {Γ} → Ctx⇒ Γ Γ
        CtxId i = var (V i)

        SubstId : ∀ {Γ} → Subst Γ Γ
        SubstId (V i) = var (V i)

        idᵣ : ∀ {Γ} → (CtxId {Γ}) ᵀ ≈ₛ SubstId {Γ}
        idᵣ (V i) = refl

        --DVecExtensionality : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {f : A → Set ℓ} → (a b : dmap f v) → (∀ {i} → a i ≡ b i) → a ≡ b
        --DVecExtensionality a b = {!   !}
        --DVecExtensionality a b = {!   !}

        subid : ∀ {Γ A i} (x : Γ ⊢ A ⟦ i ⟧) → sub SubstId x ≡ x
        subid (var (V i)) = refl
        subid (fun f x) = cong (fun f) (DExtId subid x) --(≅-to-≡ (DGrop (λ { 𝒶 𝓫 → {!  !} }) _ x))

        assoc : ∀ {i τ} {A B C : Ctx} {f : Ctx⇒ A B} {g : Ctx⇒ B C} (x : C ⊢ τ ⟦ i ⟧)
              → sub (f ᵀ) (sub (g ᵀ) x) ≡ sub ((λ x → sub (f ᵀ) (g x)) ᵀ) x
        assoc (var (V _)) = refl
        assoc (fun 𝑓 x) = cong (fun 𝑓) {!  !}  --(Ext λ i → assoc (x i))
           where
             thm : ∀ {i τ n} {A B C : Ctx} {f : Ctx⇒ A B} {g : Ctx⇒ B C} {x : C ⊢ τ ⟦ i ⟧}
                 → (e : Vec {!   !} n)
                 → (x : D.map (λ τᵢ → C ⊢ τᵢ ⟦ i ⟧) e)
                 → D.dmap (sub (f ᵀ)) (D.dmap (sub (g ᵀ)) x) ≡ D.dmap (sub ((λ σ → sub (f ᵀ) (g σ)) ᵀ)) x
             thm {f = f} {g = g} {x = x} [] (lift _) = refl
             thm {f = f} {g = g} {x = x} (_ ∷ e) (fst , snd) rewrite thm {f = f} {g = g} {x = x} e snd = {!  refl !}
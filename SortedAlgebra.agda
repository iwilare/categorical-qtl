{-# OPTIONS --sized-types #-}

open import Data.Vec as V using () renaming (Vec to Vector)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import DVec

open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Maybe using (Maybe)
open import Level renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Size
open import Function using () renaming (_∘_ to _∘′_)
open import Relation.Binary

module _ {ℓ} where

ℓ′ = sucℓ ℓ

record FunctionSignature (Σ : Set ℓ) : Set ℓ where
  constructor from_to_
  field
    {arity} : ℕ
    τ*      : Vector Σ arity
    τ       : Σ

record Signature : Set ℓ′ where
  open FunctionSignature

  field
    Σ : Set ℓ
    𝓕 : Set ℓ
    sign : 𝓕 → FunctionSignature Σ

  args = τ* ∘′ sign
  ret  = τ  ∘′ sign

record Σ-Algebra (SΣ : Signature) : Set ℓ′ where

  open Signature SΣ

  field
    S : Σ → Set ℓ

  ₀ = S

  argTypes : 𝓕 → Set ℓ
  argTypes f = map S (args f)

  retType : 𝓕 → Set ℓ
  retType f = S (ret f)

  field
    F : ∀ (f : 𝓕) → argTypes f → retType f

record Σ-Homorel {SΣ : Signature} (A : Σ-Algebra SΣ) (B : Σ-Algebra SΣ) : Set ℓ′ where

  open Signature SΣ

  module A = Σ-Algebra A
  module B = Σ-Algebra B

  field
    ρ      : {τ : Σ} → REL (A.₀ τ) (B.₀ τ) ℓ
    ρ-homo :
      ∀ (f : 𝓕)
      → (as : A.argTypes f)
      → (bs : B.argTypes f)
      → dzip ρ as bs
      → ρ (A.F f as) (B.F f bs)

record Σ-Homomorphism (SΣ : Signature) (A : Σ-Algebra SΣ) (B : Σ-Algebra SΣ) : Set ℓ′ where

  open Signature SΣ

  module A = Σ-Algebra A
  module B = Σ-Algebra B

  field
    h      : {τ : Σ} → A.₀ τ → B.₀ τ
    h-homo :
      ∀ (f : 𝓕)
      → (as : A.argTypes f)
      → h (A.F f as) ≡ B.F f (dmap h as)

module Terms (SΣ : Signature) where

  open Signature SΣ

  Ctx : Set ℓ
  Ctx = ∃[ n ] Vector Σ n

  _[_] : (Γ : Ctx) → Fin (fst Γ) → Σ
  (_ , Γ) [ i ] = V.lookup Γ i

  data _⊢_⟨_⟩ : Ctx → Σ → Size → Set ℓ where
    var : ∀ {Γ}
        → (i : Fin (fst Γ))
          ----------------------------
        → Γ ⊢ (Γ [ i ]) ⟨ ∞ ⟩
    fun : ∀ {i Γ}
        → (f : 𝓕)
        → map (Γ ⊢_⟨ i ⟩) (args f)
          ------------------------
        → Γ ⊢ ret f ⟨ ↑ i ⟩


  #_ : ∀ {Γ} → (i : Fin (fst Γ)) → Γ ⊢ (Γ [ i ]) ⟨ ∞ ⟩
  #_ = var

  _$_ : ∀ {i Γ} → (f : 𝓕) → map (Γ ⊢_⟨ i ⟩) (args f) → Γ ⊢ ret f ⟨ ↑ i ⟩
  _$_ = fun

  infix 30 #_
  infix 27 _$_

  _⊢_ : {i : Size} → Ctx → Σ → Set ℓ
  _⊢_ {i} Γ τ = Γ ⊢ τ ⟨ i ⟩

  Subst : Ctx → Ctx → Set ℓ
  Subst Γ Δ = ∀ i → Δ ⊢ V.lookup (snd Γ) i

  sub : ∀ {Γ Δ}
      → Subst Γ Δ
        -------------------------------------
      → (∀ {i A} → Γ ⊢ A ⟨ i ⟩ → Δ ⊢ A ⟨ i ⟩)
  sub σ (var x)   = σ x
  sub σ (fun f x) = fun f (dmap (sub σ) x)

  id : ∀ {Γ} → Subst Γ Γ
  id = var

  _∘_ : ∀ {A B C} → Subst B C → Subst A B → Subst A C
  (f ∘ g) i = sub f (g i)

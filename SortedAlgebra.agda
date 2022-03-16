{-# OPTIONS --sized-types #-}

open import Data.Vec            using (Vec; _∷_; []; lookup; map; zip)
open import Data.Vec.Functional using () renaming (Vector to Assoc)

import DVec            as D
import DVec.Functional as F

open import Data.Fin
open import Data.Nat
open import Data.Maybe using (Maybe)
open import Level renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality
open import Size
open import Relation.Binary

module _ {ℓ} where

ℓ′ = sucℓ ℓ

record FunctionSignature (Σ : Set ℓ) : Set ℓ where
  constructor F<_,_,_>
  field
    arity : ℕ
    τ*    : Vec Σ arity
    τ     : Σ

record Signature : Set ℓ′ where
  open FunctionSignature

  field
    Σ : Set ℓ
    𝓕 : Set ℓ
    sign : 𝓕 → FunctionSignature Σ

  args = τ* ∘ sign
  ret  = τ  ∘ sign

record Σ-Algebra (SΣ : Signature) : Set ℓ′ where

  open Signature SΣ

  field
    S : Σ → Set ℓ

  ₀ = S

  argTypes : 𝓕 → Set ℓ
  argTypes f = D.map S (args f)

  retType : 𝓕 → Set ℓ
  retType f = S (ret f)

  field
    F : ∀ (f : 𝓕) → argTypes f → retType f

record Σ-Homorel (SΣ : Signature) (A : Σ-Algebra SΣ) (B : Σ-Algebra SΣ) : Set ℓ′ where

  open Signature SΣ

  module A = Σ-Algebra A
  module B = Σ-Algebra B

  field
    ρ      : {τ : Σ} → REL (A.₀ τ) (B.₀ τ) ℓ
    ρ-homo :
      ∀ (f : 𝓕)
      → (as : A.argTypes f)
      → (bs : B.argTypes f)
      → D.dzip ρ as bs
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
       → h (A.F f as) ≡ B.F f (D.dmap h as)

module Terms (SΣ : Signature) where

    open Signature SΣ

    infix 2 _∋_

    Ctx : Set ℓ
    Ctx = ∃[ n ] Assoc Σ n

    data _∋_ : Ctx → Σ → Set ℓ where
      V : ∀ {n Γ}
          → (i : Fin n)
            -------------
          → (n , Γ) ∋ Γ i

    data _⊢_⟦_⟧ : Ctx → Σ → Size → Set ℓ where
      var : ∀ {Γ τ}
          → Γ ∋ τ
            -----------
          → Γ ⊢ τ ⟦ ∞ ⟧
      fun : ∀ {i Γ}
          → (f : 𝓕)
          → D.map (λ τᵢ → Γ ⊢ τᵢ ⟦ i ⟧) (args f)
            --------------------------------
          → Γ ⊢ ret f ⟦ ↑ i ⟧

    _⊢_ : {i : Size} → Ctx → Σ → Set ℓ
    _⊢_ {i} = _⊢_⟦ i ⟧

    Subst : Ctx → Ctx → Set ℓ
    Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

    sub : ∀ {Γ Δ}
      → Subst Γ Δ
        ---------------------------------
      → (∀ {i A} → Γ ⊢ A ⟦ i ⟧ → Δ ⊢ A ⟦ i ⟧)
    sub σ (var x)   = σ x
    sub σ (fun f x) = fun f (D.dmap (sub σ) x)
{-# OPTIONS --sized-types #-}

open import Data.Vec.Functional using (Vector)
open import Data.Fin
open import Data.Nat
open import Data.Maybe using (Maybe)
open import Level renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality
open import Size

open import DVec

record FunctionSymbol (Σ : Set) : Set where
  constructor F<_,_,_>
  field
    m    : ℕ
    args : Vector Σ m
    ret  : Σ

  τ* = args
  τ  = ret

record Signature : Set₁ where
  field
    Σ : Set
    𝒇 : ℕ
    𝓕 : Vector (FunctionSymbol Σ) 𝒇

record Σ-Algebra (SΣ : Signature) : Set₁ where

  open Signature SΣ
  open FunctionSymbol

  field
    S : Σ → Set
    F : dmap (λ { F< _ , τ* , τ > → dmap S τ* → S τ }) 𝓕

  ₀ = S

  argTypes : Fin 𝒇 → Set
  argTypes 𝒇 = dmap S (args (𝓕 𝒇))

_⇀_ : Set → Set → Set
A ⇀ B = A → Maybe B

record Σ-Homomorphism (SΣ : Signature) (A : Σ-Algebra SΣ) (B : Σ-Algebra SΣ) : Set₁ where

  open Signature SΣ
  open FunctionSymbol

  module A = Σ-Algebra A
  module B = Σ-Algebra B

  field
    ρ      : {τ : Σ} → A.₀ τ → B.₀ τ
    ρ-homo :
       ∀ (πᵢ : Fin 𝒇)
       → (as : A.argTypes πᵢ)
       → ρ (A.F πᵢ as) ≡ B.F πᵢ (map ρ as)

module Terms (SΣ : Signature) where

    open Signature SΣ
    open FunctionSymbol

    infix 2 _∋_

    Ctx : Set
    Ctx = ∃[ n ] Vector Σ n

    _∷_ : Σ → Ctx → Ctx
    x ∷ (n , xs) = _ , x Data.Vec.Functional.∷ xs

    data _∋_ : Ctx → Σ → Set where
      V : ∀ {n Γ}
          → (i : Fin n)
            -------------
          → (n , Γ) ∋ Γ i

    data _⊢_⟦_⟧ : Ctx → Σ → Size → Set where
      var : ∀ {Γ τ}
          → Γ ∋ τ
            -----------
          → Γ ⊢ τ ⟦ ∞ ⟧
      fun : ∀ {i Γ}
          → (f : Fin 𝒇)
          → dmap (λ τᵢ → Γ ⊢ τᵢ ⟦ i ⟧) (args (𝓕 f))
            --------------------------------
          → Γ ⊢ ret (𝓕 f) ⟦ ↑ i ⟧

    _⊢_ : {i : Size} → Ctx → Σ → Set
    _⊢_ {i} = _⊢_⟦ i ⟧

    Subst : Ctx → Ctx → Set
    Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

    sub : ∀ {Γ Δ}
      → Subst Γ Δ
        ---------------------------------
      → (∀ {i A} → Γ ⊢ A ⟦ i ⟧ → Δ ⊢ A ⟦ i ⟧)
    sub σ (var x)   = σ x
    sub σ (fun f x) = fun f (map (sub σ) x)
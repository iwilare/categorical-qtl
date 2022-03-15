{-# OPTIONS --sized-types #-}

open import Data.Vec            using (Vec)
open import Data.Vec.Functional using () renaming (Vector to Assoc)
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

open import DVec

module _ {ℓ} where

ℓ′ = sucℓ ℓ

record FunctionSymbol (Σ : Set ℓ) : Set ℓ where
  constructor F<_,_,_>
  field
    m    : ℕ
    args : Vec Σ m
    ret  : Σ

  τ* = args
  τ  = ret

record Signature : Set ℓ′ where
  field
    Σ : Set ℓ
    𝒇 : ℕ
    𝓕 : Assoc (FunctionSymbol Σ) 𝒇

record Σ-Algebra (SΣ : Signature) : Set ℓ′ where

  open Signature SΣ
  open FunctionSymbol

  field
    S : Σ → Set ℓ
    F : admap (λ { F< _ , τ* , τ > → dmap S τ* → S τ }) 𝓕

  ₀ = S

  argTypes : Fin 𝒇 → Set ℓ
  argTypes 𝒇 = dmap S (args (𝓕 𝒇))

record Σ-Homorel (SΣ : Signature) (A : Σ-Algebra SΣ) (B : Σ-Algebra SΣ) : Set ℓ′ where

  open Signature SΣ
  open FunctionSymbol

  module A = Σ-Algebra A
  module B = Σ-Algebra B

  field
    ρ      : {τ : Σ} → REL (A.₀ τ) (B.₀ τ) ℓ
    ρ-homo :
      ∀ (f : Fin 𝒇)
      → (as : A.argTypes f)
      → (bs : B.argTypes f)
      → zip ρ as bs
      → ρ (A.F f as) (B.F f bs)

record Σ-Homomorphism (SΣ : Signature) (A : Σ-Algebra SΣ) (B : Σ-Algebra SΣ) : Set ℓ′ where

  open Signature SΣ
  open FunctionSymbol

  module A = Σ-Algebra A
  module B = Σ-Algebra B

  field
    h      : {τ : Σ} → A.₀ τ → B.₀ τ
    h-homo :
       ∀ (f : Fin 𝒇)
       → (as : A.argTypes f)
       → h (A.F f as) ≡ B.F f (map h as)

module Terms (SΣ : Signature) where

    open Signature SΣ
    open FunctionSymbol

    infix 2 _∋_

    Ctx : Set ℓ
    Ctx = ∃[ n ] Assoc Σ n

    _∷_ : Σ → Ctx → Ctx
    x ∷ (n , xs) = _ , x Data.Vec.Functional.∷ xs

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
          → (f : Fin 𝒇)
          → dmap (λ τᵢ → Γ ⊢ τᵢ ⟦ i ⟧) (args (𝓕 f))
            --------------------------------
          → Γ ⊢ ret (𝓕 f) ⟦ ↑ i ⟧

    _⊢_ : {i : Size} → Ctx → Σ → Set ℓ
    _⊢_ {i} = _⊢_⟦ i ⟧

    Subst : Ctx → Ctx → Set ℓ
    Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

    sub : ∀ {Γ Δ}
      → Subst Γ Δ
        ---------------------------------
      → (∀ {i A} → Γ ⊢ A ⟦ i ⟧ → Δ ⊢ A ⟦ i ⟧)
    sub σ (var x)   = σ x
    sub σ (fun f x) = fun f (map (sub σ) x)
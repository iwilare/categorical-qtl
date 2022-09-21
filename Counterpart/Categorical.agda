{-# OPTIONS --sized-types #-}

module Counterpart.Categorical where

open import Data.Product using (_,_; proj₁; proj₂; <_,_>)
open import Data.Fin using (Fin)
open import Data.Vec as V using (Vec; []; _∷_)
open import Level using (lift; lower) renaming (suc to sucℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Functor
open import Categories.Category

open import VecT
open import RelPresheaves using (RelPresheaf)
open import SortedAlgebra using (Signature)

module ContextPresheaf {ℓ} {W : Category ℓ ℓ ℓ} {𝓢 : Set ℓ} (⟦_⟧ : 𝓢 → RelPresheaf W) where

  open Functor

  ⟦_⟧* : ∀ {n} → Vec 𝓢 n → RelPresheaf W
  ⟦ Γ ⟧* =
      record
      { F₀ = λ ω → mapT (λ Σ → F₀ (⟦ Σ ⟧) ω) Γ
      ; F₁ = λ f → zip (λ {Σ} → F₁ (⟦ Σ ⟧) f)

      ; identity = (λ x → lift (zip-ext (zip-imply (λ y → lower (proj₁ (identity (⟦ _ ⟧)) y)) x)))
                  , λ { (lift refl) → zip-imply (λ { refl → proj₂ (identity (⟦ _ ⟧)) (lift refl) }) zip-id }
      ; homomorphism = (λ x → zip-rel-decomp (zip-imply (proj₁ (homomorphism (⟦ _ ⟧))) x))
                      , (λ { (_ , b , c) → zip-imply (proj₂ (homomorphism (⟦ _ ⟧))) (zip-rel-comp b c) })
      ; F-resp-≈ = λ f≈g
                  → (λ { x → zip-imply (proj₁ (F-resp-≈ (⟦ _ ⟧) f≈g)) x })
                  , (λ { x → zip-imply (proj₂ (F-resp-≈ (⟦ _ ⟧) f≈g)) x })

      }

record CounterpartWModel {ℓ} (Σ : Signature {ℓ}) : Set (sucℓ ℓ) where

  open Signature Σ
  open SortedAlgebra.Term Σ hiding (_∘_)

  field
      W : Category ℓ ℓ ℓ

  open RelPresheaves W hiding (RelPresheaf)
  open Category RelPresheaves using (_∘_)

  field
      ⟦_⟧ : ∀ (τ : 𝓢) → RelPresheaf W

  open ContextPresheaf (⟦_⟧) public

  field
      I : ∀ (f : 𝓕) → RelPresheaf⇒ ⟦ args f ⟧* ⟦ ret f ⟧

  πᵢ : ∀ {n} {Γ : Ctx n} 
     → (i : Fin n)
     → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ V.lookup Γ i ⟧
  πᵢ i = record { η       = lookup i
                  ; imply = lookup-zip i
                  }

  ⟨_⟩* : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m}
          → mapT (λ τ → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ τ ⟧) Γ′
          → RelPresheaf⇒ (⟦ Γ ⟧*) (⟦ Γ′ ⟧*)
  ⟨_⟩* {Γ′ = []} * =
          record { η = λ _ → *
                 ; imply = λ _ → *
                 }
  ⟨_⟩* {Γ′ = _ ∷ _} (x , xs) =
      let module x  = RelPresheaf⇒ x
          module xs = RelPresheaf⇒ (⟨ xs ⟩*)
      in record { η     = < x.η , xs.η >
                ; imply = < x.imply , xs.imply >
                }

  ⟦_⟧ᵗ : ∀ {i n τ} {Γ : Ctx n}
          → Γ ⊢ τ ⟨ i ⟩
          → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ τ ⟧
  ⟦ var i ⟧ᵗ   = πᵢ i
  ⟦ fun f x ⟧ᵗ = I f ∘ ⟨ map ⟦_⟧ᵗ x ⟩*

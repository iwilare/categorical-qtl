{-# OPTIONS --sized-types #-}

open import Categories.Category
open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Complete
open import Categories.Category.Complete.Finitely
open import Categories.Category.Complete.Properties
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Rels
open import Categories.Category.Slice
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation
open import Categories.Object.Terminal
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open Categories.Functor.Functor using (F₀; F₁; identity; homomorphism; F-resp-≈)

open import SortedAlgebra
open import DVec
open import RelPresheaves using (RelPresheaf)

open import Data.Vec as V using () renaming (Vec to Vector)
open import Data.Product using (_,_; proj₁; proj₂; <_,_>)
open import Data.Fin using (Fin)
open import Data.Unit.Polymorphic hiding (tt)
open import Data.Unit.Base using (tt)

private
  variable
    ℓ : Level

module ContextPresheaf {ℓ} {W : Category ℓ ℓ ℓ} {Σ : Set ℓ} (⟦_⟧ : Σ → RelPresheaf W) where

  ⟦_⟧* : ∀ {n} → Vector Σ n → RelPresheaf W
  ⟦ Γ ⟧* =
    record
      { F₀ = λ σ → DVec.map (λ Σ → F₀ (⟦ Σ ⟧) σ) Γ
      ; F₁ = λ f → DVec.dzip (F₁ (⟦ _ ⟧) f)
      ; identity = (λ x → lift (dzip-ext (dzip-imply (λ y → lower (proj₁ (identity (⟦ _ ⟧)) y)) x)))
                 , λ { (lift refl) → dzip-imply (λ { refl → proj₂ (identity (⟦ _ ⟧)) (lift refl) }) dzip-id }
      ; homomorphism = (λ x → dzip-rel-decomp (dzip-imply (proj₁ (homomorphism (⟦ _ ⟧))) x))
                     , (λ { (_ , b , c) → dzip-imply (proj₂ (homomorphism (⟦ _ ⟧))) (dzip-rel-comp b c) })
      ; F-resp-≈ = λ f≈g
                 → (λ { x → dzip-imply (proj₁ (F-resp-≈ (⟦ _ ⟧) f≈g)) x })
                 , (λ { x → dzip-imply (proj₂ (F-resp-≈ (⟦ _ ⟧) f≈g)) x })
      }

record CounterpartWModel {ℓ} (SΣ : Signature {ℓ}) : Set (suc ℓ) where
  open Signature SΣ
  open Terms (SΣ) renaming (_∘_ to _∘ᶜ_)

  field
    W : Category ℓ ℓ ℓ

  open RelPresheaves W hiding (RelPresheaf)
  open Category RelPresheaves using (_∘_)

  field
    ⟦_⟧ : ∀ (τ : Σ) → RelPresheaf W

  open ContextPresheaf (⟦_⟧) public

  field
    I : ∀ (f : 𝓕) → RelPresheaf⇒ ⟦ args f ⟧* ⟦ ret f ⟧

  πᵢ : ∀ {n} {Γ : Vector Σ n} → (i : Fin n) → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ V.lookup Γ i ⟧
  πᵢ i = record { η    = lookup i
               ; imply = lookup-dzip i
               }

  ⟨_⟩* : ∀ {n m}
       → {Γ : Vector Σ n} {Γ′ : Vector Σ m}
       → map (λ τ → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ τ ⟧) Γ′
       → RelPresheaf⇒ (⟦ Γ ⟧*) (⟦ Γ′ ⟧*)
  ⟨_⟩* {Γ′ = V.[]} (lift tt) = record { η = λ _ → lift tt ; imply = λ _ → lift tt }
  ⟨_⟩* {Γ′ = _ V.∷ _} (x , v) =
    let module x = RelPresheaf⇒ x
        module v = RelPresheaf⇒ (⟨ v ⟩*)
     in record { η     = < x.η , v.η >
               ; imply = < x.imply , v.imply >
               }

  ⟦_⟧ᵗ : ∀ {i n τ} {Γ : Vector Σ n} → (n , Γ) ⊢ τ ⟨ i ⟩ → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ τ ⟧
  ⟦ var i ⟧ᵗ   = πᵢ i
  ⟦ fun f x ⟧ᵗ = I f ∘ ⟨ dmap ⟦_⟧ᵗ x ⟩*
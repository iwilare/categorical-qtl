{-# OPTIONS --sized-types #-}

open import Level
open import Relation.Binary
open import Categories.Category
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Rels
open import Categories.Functor.Presheaf
open import Categories.Category.Construction.Properties.Presheaves.Cartesian as C
open C.IsCartesian
open import Categories.Category.Complete
open import Categories.NaturalTransformation
open import Categories.Category.Complete.Finitely
open import Categories.Functor
open import Categories.Category.Complete.Properties
open import Categories.Category.BinaryProducts
open import Categories.Object.Terminal
open import Relation.Binary.PropositionalEquality

open import SortedAlgebra
open import DVec
import RelPresheaves

open import Data.Vec as V using () renaming (Vec to Vector)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using (Fin)

private
  variable
    ℓ : Level

record CounterpartFrame : Set (suc ℓ) where
  field
    W : Set ℓ
    D : W → Set ℓ
    R : Rel W ℓ
    C : (w₁ : W) → (w₂ : W) → REL (D w₁) (D w₂) ℓ

record CounterpartModel (SΣ : Signature {ℓ}) : Set (suc ℓ)  where
  open Signature SΣ
  field
    W      : Set ℓ
    d      : W → Σ-Algebra SΣ
    _⇝_[_] : (w₁ : W) → (w₂ : W) → (cr : Σ-Homorel SΣ (d w₁) (d w₂)) → Set ℓ

record CounterpartWModel {ℓ} (SΣ : Signature {ℓ}) : Set (suc ℓ) where
  open Signature SΣ
  open Terms (SΣ)
  open Categories.Functor.Functor using (F₀; F₁; identity; homomorphism; F-resp-≈)

  field
    W : Category ℓ ℓ ℓ

  open RelPresheaves W

  field
    ⟦_⟧ : ∀ (τ : Σ) → RelPresheaf

  ⟦_⟧* : ∀ {n} → Vector Σ n → RelPresheaf
  ⟦ Γ ⟧* = record
    { F₀ = λ σ → DVec.map (λ Σ → F₀ (⟦ Σ ⟧) σ) Γ
    ; F₁ = λ f → DVec.dzip (F₁ (⟦ _ ⟧) f)
    ; identity = (λ x → lift (zipext (ddzip (λ {m} x → lower (proj₁ (Functor.identity (⟦ m ⟧)) x)) x)))
               , λ { (lift refl) → ddzip (λ { {m} refl → proj₂ (Functor.identity (⟦ m ⟧)) (lift refl) }) dzipid }
    ; homomorphism = zipdecomp (proj₁ (Functor.homomorphism (⟦ _ ⟧)))
                   , (λ { (_ , b , c) → zipcomp (λ {σ} x x₁ → proj₂ (Functor.homomorphism (⟦ σ ⟧)) (_ , (x , x₁))) b c })
    ; F-resp-≈ = λ f≈g
               → (λ { x → ddzip (proj₁ (Functor.F-resp-≈ (⟦ _ ⟧) f≈g)) x })
               , (λ { x → ddzip (proj₂ (Functor.F-resp-≈ (⟦ _ ⟧) f≈g)) x })
    }

  field
    I : ∀ (f : 𝓕) → NaturalTransformation ⟦ args f ⟧* ⟦ ret f ⟧

  πᵢ : ∀ {n} {Γ : Vector Σ n} → (i : Fin n) → RelPresheaf⇒ (⟦ Γ ⟧*) ⟦ V.lookup Γ i ⟧
  πᵢ i = record { η = lookup i ; imply = ziplookup i }

  ⟦_⟧ᵗ : ∀ {Γ τ} → Γ ⊢ τ → RelPresheaf⇒ ⟦ Γ ⟧* ⟦ τ ⟧
  ⟦ var i ⟧ᵗ   = {!  !}
  ⟦ fun f x ⟧ᵗ = {!   !}
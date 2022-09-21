{-# OPTIONS --sized-types #-}

module Counterpart.Categorical.TemporalStructure where

open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_) renaming (suc to sucℓ)
open import Relation.Unary using (Pred; _∈_)

open import Size using (Size; ∞; ↑_; Size<_)
open import Codata.Thunk as Thunk using (Thunk; force)

open import Categories.Functor hiding (id)
open import Categories.Category

open import VecT
open import RelPresheaves using (RelPresheaf)
open import SortedAlgebra using (Signature)

record TemporalStructure {co cℓ ce} (W : Category co cℓ ce) : Set (sucℓ (co ⊔ cℓ)) where
  constructor TStructure 
  open Category W

  field
    T : ∀ {A B}
      → Pred (A ⇒ B) cℓ

  data Path (A : Obj) (i : Size) : Set (co ⊔ cℓ) where
    _⟶_ : ∀ {B}
        → (arr : A ⇒ B)
        → {arr ∈ T}
        → Thunk (Path B) i
        → Path A i

  next : ∀ {A i} → Path A i → Obj
  next (_⟶_ {B} _ _) = B

  arr : ∀ {A} → (p : Path A ∞) → A ⇒ next p
  arr (a ⟶ _) = a

  tail : ∀ {A i} {j : Size< i} → (p : Path A i) → Path (next p) j
  tail (_ ⟶ p) = p .force

  obj : ∀ {A} → Path A ∞ → ℕ → Obj
  obj {A} p zero = A
  obj p (suc i) = obj (tail p) i

  compose≤ : ∀ {A} → (p : Path A ∞) → (n : ℕ) → A ⇒ obj p n
  compose≤ p zero = id
  compose≤ p (suc i) = compose≤ (tail p) i ∘ arr p

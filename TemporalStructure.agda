{-# OPTIONS --sized-types #-}

open import Categories.Category

module TemporalStructure {co cℓ ce} (C : Category co cℓ ce) where

open import Level

open Category C

open import Data.Vec as V using () renaming (Vec to Vector)
open import Data.Vec.Membership.Propositional
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; -,_; ∃-syntax) renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    ℓ : Level

record TemporalStructure : Set (co ⊔ cℓ) where

  field
    arrows : (A : Obj) → ∃[ n ] (Vector (∃[ B ] (A ⇒ B)) n)

  record Path (A : Obj) : Set (co ⊔ cℓ) where
    constructor _∷_
    coinductive

    field
      {B}   : Obj
      {arr} : A ⇒ B
      ins   : (B , arr) ∈ snd (arrows A)
      next  : Path B

  lookup : ∀ {A} → Path A → (i : ℕ) → ∃[ B ] Path B
  lookup p zero    = -, p
  lookup p (suc i) = lookup (Path.next p) i

  comp : ∀ {A} → Path A → (i : ℕ) → ∃[ B ] (A ⇒ B)
  comp p zero    = -, id
  comp p (suc i) = -, snd (comp (Path.next p) i) ∘ Path.arr p
{-# OPTIONS --sized-types #-}

open import Level
open import Categories.Category

open import Data.Vec as V using () renaming (Vec to Vector)
open import Data.Vec.Membership.Propositional
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; -,_; ∃-syntax) renaming (proj₁ to fst; proj₂ to snd)

record TemporalStructure {co cℓ ce} (W : Category co cℓ ce) : Set (co ⊔ cℓ) where
  constructor TStructure

  open Category W

  field
    arrows : (A : Obj) → ∃[ n ] (Vector (∃[ B ] (A ⇒ B)) n)

  record Path (A : Obj) : Set (co ⊔ cℓ) where
    constructor _⟶_
    coinductive

    field
      {B}   : Obj
      {arr} : A ⇒ B
      ins   : (B , arr) ∈ snd (arrows A)
      next  : Path B

  drop : ∀ {A} → Path A → (i : ℕ) → ∃[ B ] Path B
  drop p zero    = -, p
  drop p (suc i) = drop (Path.next p) i

  comp : ∀ {A} → Path A → (i : ℕ) → ∃[ B ] (A ⇒ B)
  comp p zero    = -, id
  comp p (suc i) = -, snd (comp (Path.next p) i) ∘ Path.arr p
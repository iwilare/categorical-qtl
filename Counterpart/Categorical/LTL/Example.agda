{-# OPTIONS --sized-types #-}

open import SortedAlgebra
open import Counterpart.Categorical.TemporalModel

module Counterpart.Categorical.LTL.Example where

open import Data.Nat

open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)
open import Size using (Size; ∞; ↑_; Size<_)
open import Data.Vec using (_∷_; [])
open import Level using (lift)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_; ε)

open import Codata.Thunk as Thunk using (Thunk; force)

import Data.Unit
pattern * = lift Data.Unit.tt

data Gr-Sorts : Set where
  Edge : Gr-Sorts
  Node : Gr-Sorts

data Gr-Functions : Set where
  s : Gr-Functions
  t : Gr-Functions

Gr : Signature
Gr = record { 𝓢 = Gr-Sorts
            ; 𝓕 = Gr-Functions
            ; sign𝓕 = λ { s → [ Edge ] ↦ Node
                        ; t → [ Edge ] ↦ Node
                        }
            } where open import Data.Vec using ([_])

data G₀-Edges : Set where e0 e1 e2 : G₀-Edges
data G₀-Nodes : Set where n0 n1 n2 : G₀-Nodes

G₀ : Σ-Algebra Gr
G₀ = record { S = λ { Edge → G₀-Edges ; Node → G₀-Nodes }
            ; F = λ { s → λ { (e0 , *) → n0
                            ; (e1 , *) → n1
                            ; (e2 , *) → n2
                            }
                    ; t → λ { (e0 , *) → n1
                            ; (e1 , *) → n2
                            ; (e2 , *) → n0
                            }
                    }
            }

data G₁-Edges : Set where e3 e4 : G₁-Edges
data G₁-Nodes : Set where n3 n4 : G₁-Nodes

G₁ : Σ-Algebra Gr
G₁ = record { S = λ { Edge → G₁-Edges ; Node → G₁-Nodes }
            ; F = λ { s → λ { (e3 , *) → n3
                            ; (e4 , *) → n4
                            }
                    ; t → λ { (e3 , *) → n4
                            ; (e4 , *) → n3
                            }
                    }
            }

data G₂-Edges : Set where e5 : G₂-Edges
data G₂-Nodes : Set where n5 : G₂-Nodes

G₂ : Σ-Algebra Gr
G₂ = record { S = λ { Edge → G₂-Edges ; Node → G₂-Nodes }
            ; F = λ { s → λ { (e5 , *) → n5
                            }
                    ; t → λ { (e5 , *) → n5
                            }
                    }
            }

data F₀-Edges : G₀-Edges → G₁-Edges → Set where
  e0e4 : F₀-Edges e0 e4
  e1e3 : F₀-Edges e1 e3

data F₀-Nodes : G₀-Nodes → G₁-Nodes → Set where
  n0n4 : F₀-Nodes n0 n4
  n1n3 : F₀-Nodes n1 n3
  n2n4 : F₀-Nodes n2 n4

F₀ : Σ-Rel G₀ G₁
F₀ = record { ρ = λ { {Edge} → F₀-Edges
                    ; {Node} → F₀-Nodes
                    }
            ; ρ-homo = λ { s (e0e4 , *) → n0n4
                          ; s (e1e3 , *) → n1n3
                          ; t (e0e4 , *) → n1n3
                          ; t (e1e3 , *) → n2n4
                          }
            }

data F₁-Edges : G₁-Edges → G₂-Edges → Set where
  e3e5₁ : F₁-Edges e3 e5
data F₁-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₁ : F₁-Nodes n3 n5
  n4n5₁ : F₁-Nodes n4 n5

F₁ : Σ-Rel G₁ G₂
F₁ = record { ρ = λ { {Edge} → F₁-Edges
                    ; {Node} → F₁-Nodes
                    }
            ; ρ-homo = λ { s (e3e5₁ , *) → n3n5₁
                          ; t (e3e5₁ , *) → n4n5₁
                          }
            }

data F₂-Edges : G₁-Edges → G₂-Edges → Set where
  e4e5₂ : F₂-Edges e4 e5
data F₂-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₂ : F₂-Nodes n3 n5
  n4n5₂ : F₂-Nodes n4 n5

F₂ : Σ-Rel G₁ G₂
F₂ = record { ρ = λ { {Edge} → F₂-Edges
                    ; {Node} → F₂-Nodes
                    }
            ; ρ-homo = λ { s (e4e5₂ , *) → n4n5₂
                          ; t (e4e5₂ , *) → n3n5₂
                          }
            }

data F₃-Edges : G₂-Edges → G₂-Edges → Set where
  e5e5 : F₃-Edges e5 e5
data F₃-Nodes : G₂-Nodes → G₂-Nodes → Set where
  n5n5 : F₃-Nodes n5 n5

F₃ : Σ-Rel G₂ G₂
F₃ = record { ρ = λ { {Edge} → F₃-Edges
                    ; {Node} → F₃-Nodes
                    }
            ; ρ-homo = λ { s (e5e5 , *) → n5n5
                          ; t (e5e5 , *) → n5n5
                          }
            }

data W : Set where
  ω₀ ω₁ ω₂ : W

data _⇝_ : W → W → Set where
  f₀    : ω₀ ⇝ ω₁
  f₁ f₂ : ω₁ ⇝ ω₂
  f₃    : ω₂ ⇝ ω₂

d : W → Σ-Algebra Gr
d ω₀ = G₀
d ω₁ = G₁
d ω₂ = G₂

f : ∀ {A B} → A ⇝ B → Σ-Rel (d A) (d B)
f f₀ = F₀
f f₁ = F₁
f f₂ = F₂
f f₃ = F₃

open import LTL
open import Counterpart.Classical
open import Counterpart.ClassicalToCategorical
open import Counterpart.Categorical.TemporalStructure

M : CounterpartModel Gr
M = record { W = W ; d = d ; _⇝_ = _⇝_ ; f = f }

TWM : TemporalCounterpartWModel Gr
TWM = ClassicalToCategorical M

module TWM = TemporalCounterpartWModel TWM

open import Counterpart.Categorical.LTL.Semantics TWM
open TemporalStructure TWM.T
open Signature Gr 
open SortedAlgebra.Term Gr

module ExampleFormulae where

  open import Data.Fin using (zero; suc)

  infix 27 _$_

  _$_ : ∀ {s n} {Γ : Ctx n} f → _ → Γ ⊢ _ ⟨ ↑ s ⟩
  _$_ = fun

  v0 : ∀ {n} {Γ : Ctx (1 + n)} → Γ ⊢ _ ⟨ ∞ ⟩
  v0 = var zero

  v1 : ∀ {n} {Γ : Ctx (2 + n)} → Γ ⊢ _ ⟨ ∞ ⟩
  v1 = var (suc zero)

  present : ∀ {τ} → LTL (τ ∷ [])
  present {τ} = ∃< τ > v1 ≡ᵗ v0

  notPresent : ∀ {τ} → LTL (τ ∷ [])
  notPresent {τ} = ∀< τ > v1 ≢ᵗ v0

  nextStepPreserved : ∀ {τ} → LTL (τ ∷ [])
  nextStepPreserved = present ∧ O present

  nextStepDeallocated : ∀ {τ} → LTL (τ ∷ [])
  nextStepDeallocated = present ∧ A notPresent

  loop : ∀ {n} {Γ : Ctx n} → LTL (Edge ∷ Γ)
  loop = s $ (v0 , *) ≡ᵗ t $ (v0 , *)

  hasLoop : LTL []
  hasLoop = ∃< Edge > loop
  
  nodeHasLoop : LTL (Node ∷ [])
  nodeHasLoop = ∃< Edge > (s $ (v0 , *) ≡ᵗ v1 ∧ loop)

  willBecomeLoop : LTL (Edge ∷ [])
  willBecomeLoop = ! loop ∧ ◇ loop

  eventuallyNodeHasLoop : LTL (Node ∷ [])
  eventuallyNodeHasLoop = ◇ nodeHasLoop

open ExampleFormulae

_⇒ : ∀ {ℓ ℓ′} {A : Set ℓ} {i j : A} {R : Rel A ℓ′} → R i j → Star R i j
a ⇒ = a ◅ ε

pattern step a = a ◅ ε

exampleNextStepDeallocated : DecidableFormula (nextStepDeallocated {Edge})
exampleNextStepDeallocated ω₀ (e2 , *) =
  yes ((e2 , refl) , λ { (step f₀) _ () _ _ })
exampleNextStepDeallocated ω₀ (e0 , *) =
  no λ { ((e0 , refl) , A¬p)
        → A¬p (f₀ ⇒) (e4 , *) ((e4 , refl , e0e4) , *) e0 refl }
exampleNextStepDeallocated ω₀ (e1 , *) =
  no λ { ((e1 , refl) , A¬p)
        → A¬p (f₀ ⇒) (e3 , *) ((e3 , refl , e1e3) , *) e1 refl }
exampleNextStepDeallocated ω₁ (e3 , *) =
  no λ { ((e3 , refl) , A¬p)
        → A¬p (f₁ ⇒) (e5 , *) ((e5 , refl , e3e5₁) , *) e3 refl }
exampleNextStepDeallocated ω₁ (e4 , *) =
  no λ { ((e4 , refl) , A¬p)
        → A¬p (f₂ ⇒) (e5 , *) ((e5 , refl , e4e5₂) , *) e4 refl }
exampleNextStepDeallocated ω₂ (e5 , *) =
  no λ { ((e5 , refl) , A¬p)
        → A¬p (f₃ ⇒) (e5 , *) ((e5 , refl , e5e5) , *) e5 refl }

exampleNextStepPreserved : DecidableFormula (nextStepPreserved {Edge})
exampleNextStepPreserved ω₀ (e0 , *) =
  yes ((e0 , refl)
      , λ { (step f₀) → (e4 , *)
                    , ((e4 , refl , e0e4) , *)
                    , e0 , refl })
exampleNextStepPreserved ω₀ (e1 , *) =
  yes ((e1 , refl)
      , λ { (step f₀) → (e3 , *)
                    , ((e3 , refl , e1e3) , *)
                    , e1 , refl })
exampleNextStepPreserved ω₀ (e2 , *) =
  no λ { ((e2 , refl) , Op) → absurd (Op (f₀ ⇒)) }
    where absurd : _ → _; absurd ()
exampleNextStepPreserved ω₁ (e3 , *) =
  no λ { ((e3 , refl) , Op) → absurd (Op (f₂ ⇒)) }
    where absurd : _ → _; absurd ()
exampleNextStepPreserved ω₁ (e4 , *) =
  no λ { ((e4 , refl) , Op) → absurd (Op (f₁ ⇒)) }
    where absurd : _ → _; absurd ()
exampleNextStepPreserved ω₂ (e5 , *) =
  yes ((e5 , refl)
      , λ { (step f₃) → (e5 , *)
                    , ((e5 , refl , e5e5) , *)
                    , e5 , refl })

exampleLoop : DecidableFormula (loop {Γ = []})
exampleLoop ω₀ (e0 , *) = no (λ ())
exampleLoop ω₀ (e1 , *) = no (λ ())
exampleLoop ω₀ (e2 , *) = no (λ ())
exampleLoop ω₁ (e3 , *) = no (λ ())
exampleLoop ω₁ (e4 , *) = no (λ ())
exampleLoop ω₂ (e5 , *) = yes refl

exampleNodeHasLoop : DecidableFormula nodeHasLoop
exampleNodeHasLoop ω₀ (n0 , *) = no λ { (e0 , ()) ; (e1 , ()) ; (e2 , ()) }
exampleNodeHasLoop ω₀ (n1 , *) = no λ { (e0 , ()) ; (e1 , ()) ; (e2 , ()) }
exampleNodeHasLoop ω₀ (n2 , *) = no λ { (e0 , ()) ; (e1 , ()) ; (e2 , ()) }
exampleNodeHasLoop ω₁ (n3 , *) = no λ { (e3 , ()) ; (e4 , ()) }
exampleNodeHasLoop ω₁ (n4 , *) = no λ { (e3 , ()) ; (e4 , ()) }
exampleNodeHasLoop ω₂ (n5 , *) = yes (e5 , refl , refl)

exampleHasLoop : DecidableFormula hasLoop
exampleHasLoop ω₀ * = no λ { (e0 , ()) ; (e1 , ()) ; (e2 , ()) }
exampleHasLoop ω₁ * = no λ { (e3 , ()) ; (e4 , ()) }
exampleHasLoop ω₂ * = yes (e5 , refl)

self₂ : ∀ {i} → Path ω₂ i
self₂ = (f₃ ⇒) ⟶ λ { .force → self₂ }

path1 : ∀ {ω i} → Path ω i
path1 {ω₀} = (f₀ ⇒) ⟶ λ { .force → (f₁ ⇒) ⟶ λ { .force → self₂ } }
path1 {ω₁} = (f₁ ⇒) ⟶ λ { .force → self₂ }
path1 {ω₂} = self₂

path2 : ∀ {ω i} → Path ω i
path2 {ω₀} = (f₀ ⇒) ⟶ λ { .force → (f₂ ⇒) ⟶ λ { .force → self₂ } }
path2 {ω₁} = (f₂ ⇒) ⟶ λ { .force → self₂ }
path2 {ω₂} = self₂

exampleWillBecomeLoop : DecidableFormula willBecomeLoop
exampleWillBecomeLoop =
    λ { ω₀ (e0 , *) → no ex0
      ; ω₀ (e1 , *) → no ex1
      ; ω₀ (e2 , *) → no ex2
      ; ω₁ (e3 , *) → no ex3
      ; ω₁ (e4 , *) → no ex4
      ; ω₂ (e5 , *) → no ex5
      }
  where
    ex0 : ⟨ ! willBecomeLoop ⟩ {ω₀} (e0 , *)
    ex0 (¬loop , ◇loop) with ◇loop path1
    ... | 0 , b , (e0 , *) , ()
    ... | 0 , b , (e1 , *) , ()
    ... | 0 , b , (e2 , *) , ()
    ... | 1 , b , (e3 , *) , ()
    ... | 1 , b , (e4 , *) , ()
    ... | suc (suc a) , b , _ , ((e3 , ()) , *) , eq
    ... | suc (suc a) , b , _ , ((e4 , ()) , *) , eq

    ex1 : ⟨ ! willBecomeLoop ⟩ {ω₀} (e1 , *)
    ex1 (¬loop , ◇loop) with ◇loop path2
    ... | 0 , b , (e0 , *) , ()
    ... | 0 , b , (e1 , *) , ()
    ... | 0 , b , (e2 , *) , ()
    ... | 1 , b , (e3 , *) , ()
    ... | 1 , b , (e4 , *) , ()
    ... | suc (suc a) , b , _ , ((e3 , ()) , *) , eq
    ... | suc (suc a) , b , _ , ((e4 , ()) , *) , eq

    ex2 : ⟨ ! willBecomeLoop ⟩ {ω₀} (e2 , *)
    ex2 (¬loop , ◇loop) with ◇loop path1
    ... | 0 , p , (e2 , *) , a , n2≡n0 = ⊥-elim (¬loop n2≡n0)

    ex3 : ⟨ ! willBecomeLoop ⟩ {ω₁} (e3 , *)
    ex3 (¬loop , ◇loop) with ◇loop path2
    ... | 0 , p , (e4 , *) , a , n4≡n3 = ⊥-elim (¬loop (sym n4≡n3))
    ... | 0 , p , (e3 , *) , a , n3≡n4 = ⊥-elim (¬loop n3≡n4)

    ex4 : ⟨ ! willBecomeLoop ⟩ {ω₁} (e4 , *)
    ex4 (¬loop , ◇loop) with ◇loop path1
    ... | 0 , p , (e3 , *) , a , n3≡n4 = ⊥-elim (¬loop (sym n3≡n4))
    ... | 0 , p , (e4 , *) , a , n4≡n3 = ⊥-elim (¬loop n4≡n3)
    
    ex5 : ⟨ ! willBecomeLoop ⟩ {ω₂} (e5 , *)
    ex5 (¬loop , _) = ¬loop refl

exampleEventuallyHasLoop : DecidableFormula eventuallyNodeHasLoop
exampleEventuallyHasLoop =
    λ { ω₀ (n0 , *) → yes ex0
      ; ω₀ (n1 , *) → yes ex1
      ; ω₀ (n2 , *) → yes ex2
      ; ω₁ (n3 , *) → yes ex3
      ; ω₁ (n4 , *) → yes ex4
      ; ω₂ (n5 , *) → yes ex5
      }
  where
    ex5 : ⟨ eventuallyNodeHasLoop ⟩ {ω₂} (n5 , *)
    ex5 (step f₃ ⟶ p) =
      0 , (λ { (suc i) () })  , (n5 , *) , ((refl , *) , e5 , refl , refl)

    ex4 : ⟨ eventuallyNodeHasLoop ⟩ {ω₁} (n4 , *)
    ex4 (step f₁ ⟶ p) with p .force
    ... | step f₃ ⟶ p =
          1 , (λ { 0 (s≤s z≤n) → ((n4 , *) , (refl , *) , *) })
            , (n5 , *) , (((n5 , (refl , n4n5₁)) , *) , (e5 , (refl , refl)))
    ex4 (step f₂ ⟶ p) with p .force
    ... | step f₃ ⟶ p =
          1 , (λ { 0 (s≤s z≤n) → ((n4 , *) , (refl , *) , *) })
            , (n5 , *) , (((n5 , (refl , n4n5₂)) , *) , (e5 , (refl , refl)))

    ex3 : ⟨ eventuallyNodeHasLoop ⟩ {ω₁} (n3 , *)
    ex3 (step f₁ ⟶ p) with p .force
    ... | step f₃ ⟶ p =
          1 , (λ { 0 (s≤s z≤n) → ((n3 , *) , (refl , *) , *) })
            , (n5 , *) , (((n5 , (refl , n3n5₁)) , *) , (e5 , (refl , refl)))
    ex3 (step f₂ ⟶ p) with p .force
    ... | step f₃ ⟶ p =
          1 , (λ { 0 (s≤s z≤n) → ((n3 , *) , (refl , *) , *) })
            , (n5 , *) , (((n5 , (refl , n3n5₂)) , *) , (e5 , (refl , refl)))

    ex2 : ⟨ eventuallyNodeHasLoop ⟩ {ω₀} (n2 , *)
    ex2 (step f₀ ⟶ p) with ex4 (p .force)
    ... | n , u , p , (k , *) , m =
                      ℕ.suc n
                    , (λ { 0 (s≤s z≤n) → (n2 , *) , (refl , *) , *
                          ; (suc i) (s≤s x) →
                              let u1 , ((up , _) , _) = u i x
                              in u1 , ((n4 , up , n2n4) , *) , * })
                    , p
                    , ((n4 , k , n2n4) , *) , m

    ex1 : ⟨ eventuallyNodeHasLoop ⟩ {ω₀} (n1 , *)
    ex1 (step f₀ ⟶ p) with ex3 (p .force)
    ... | n , u , p , (k , *) , m =
                      ℕ.suc n
                    , (λ { 0 (s≤s z≤n) → (n1 , *) , (refl , *) , *
                          ; (suc i) (s≤s x) →
                              let u1 , ((up , _) , _) = u i x
                              in u1 , ((n3 , up , n1n3) , *) , * })
                    , p
                    , ((n3 , k , n1n3) , *) , m

    ex0 : ⟨ eventuallyNodeHasLoop ⟩ {ω₀} (n0 , *)
    ex0 (step f₀ ⟶ p) with ex4 (p .force)
    ... | n , u , p , (k , *) , m =
                      ℕ.suc n
                    , (λ { 0 (s≤s z≤n) → (n0 , *) , (refl , *) , *
                          ; (suc i) (s≤s x) →
                              let u1 , ((up , _) , _) = u i x
                              in u1 , ((n4 , up , n0n4) , *) , * })
                    , p
                    , ((n4 , k , n0n4) , *) , m
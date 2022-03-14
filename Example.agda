{-# OPTIONS --sized-types #-}

open import SortedAlgebra
open import Data.Vec.Functional
open import Data.Fin

data Sort : Set where
  Edge : Sort
  Node : Sort

[_] : Sort → Vector Sort 1
[ x ] = x ∷ []

Gr : Signature
Gr = record { Σ = Sort
            ; 𝒇 = _
            ; 𝓕 = F< 1 , [ Edge ] , Node > -- Source
                ∷ F< 1 , [ Edge ] , Node > -- Target
                ∷ []
            }

G₀ : Σ-Algebra Gr
G₀ = record { S = λ { Edge → Edges ; Node → Nodes }
            ; F = λ { zero       → λ args → {!   !} -- Source
                    ; (suc zero) → λ args → {!   !} -- Target
                    }
            }
   where
    data Edges : Set where
        e0 e1 e2 : Edges
    data Nodes : Set where
        n0 n1 n2 : Nodes
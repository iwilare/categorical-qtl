{-# OPTIONS --sized-types #-}

open import SortedAlgebra
open import Data.Vec using (Vec; [_])
open import Data.Vec.Functional using (_∷_; []) renaming (Vector to Assoc)
open import Data.Fin
open import Data.Product using (_,_)
open import Data.Unit.Base using (tt)
open import Level using (lift)

data Sort : Set where
  Edge : Sort
  Node : Sort

Gr : Signature
Gr = record { Σ = Sort
            ; 𝒇 = _
            ; 𝓕 = F< 1 , [ Edge ] , Node > -- Source
                ∷ F< 1 , [ Edge ] , Node > -- Target
                ∷ []
            }

G₀ : Σ-Algebra Gr
G₀ = record { S = λ { Edge → Edges ; Node → Nodes }
            ; F = λ { zero       → λ { (e0 , _) → n0
                                     ; (e1 , _) → n1
                                     ; (e2 , _) → n2 } -- Source
                    ; (suc zero) → λ { (e0 , _) → n1
                                     ; (e1 , _) → n2
                                     ; (e2 , _) → n0 } -- Target
                    }
            }
   where
    data Edges : Set where
        e0 e1 e2 : Edges
    data Nodes : Set where
        n0 n1 n2 : Nodes
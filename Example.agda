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

data Function : Set where
  s : Function
  t : Function

Gr : Signature
Gr = record { Σ = Sort
            ; 𝓕 = Function
            ; sign = λ { s → F< _ , [ Edge ] , Node >
                       ; t → F< _ , [ Edge ] , Node > }
            }

G₀ : Σ-Algebra Gr
G₀ = record { S = λ { Edge → Edges ; Node → Nodes }
            ; F = λ { s → λ { (e0 , _) → n0
                            ; (e1 , _) → n1
                            ; (e2 , _) → n2
                            }
                    ; t → λ { (e0 , _) → n1
                            ; (e1 , _) → n2
                            ; (e2 , _) → n0
                            }
                    }
            }
   where
    data Edges : Set where e0 e1 e2 : Edges
    data Nodes : Set where n0 n1 n2 : Nodes
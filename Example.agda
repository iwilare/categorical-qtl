{-# OPTIONS --sized-types #-}

open import Data.Vec        using (Vec; _∷_; [])
open import Data.Product    using (_,_; -,_)
open import Data.Unit.Base  using (tt)
open import Data.Fin        using (Fin; suc; zero)
open import Level           using (lift)
open import Function        using (_∘_; flip)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.PropositionalEquality as _≡_          using (_≡_; _≢_; refl)
open import Relation.Binary.PropositionalEquality.Properties      using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻▻_)

open import Categories.Category.Instance.Rels using (Rels)
open import Categories.Category

open import FreeCategory
open import DVec using (⊤)
open import SortedAlgebra
open import TemporalStructure
open import CounterpartAlgebraic
open import CounterpartCategorial
open import RelPresheaves
open import AlgebraicToCategorial

data ΣSort : Set where
  Edge : ΣSort
  Node : ΣSort

data ΣFunction : Set where
  s : ΣFunction
  t : ΣFunction

Gr : Signature
Gr = record { Σ = ΣSort
            ; 𝓕 = ΣFunction
            ; sign = λ { s → from Edge ∷ [] to Node
                       ; t → from Edge ∷ [] to Node }
            }

data G₀-Edges : Set where e0 e1 e2 : G₀-Edges
data G₀-Nodes : Set where n0 n1 n2 : G₀-Nodes

G₀ : Σ-Algebra Gr
G₀ = record { S = λ { Edge → G₀-Edges ; Node → G₀-Nodes }
            ; F = λ { s → λ { (e0 , ⊤) → n0
                            ; (e1 , ⊤) → n1
                            ; (e2 , ⊤) → n2
                            }
                    ; t → λ { (e0 , ⊤) → n1
                            ; (e1 , ⊤) → n2
                            ; (e2 , ⊤) → n0
                            }
                    }
            }

data G₁-Edges : Set where e3 e4 : G₁-Edges
data G₁-Nodes : Set where n3 n4 : G₁-Nodes

G₁ : Σ-Algebra Gr
G₁ = record { S = λ { Edge → G₁-Edges ; Node → G₁-Nodes }
            ; F = λ { s → λ { (e3 , ⊤) → n3
                            ; (e4 , ⊤) → n4
                            }
                    ; t → λ { (e3 , ⊤) → n4
                            ; (e4 , ⊤) → n3
                            }
                    }
            }

data G₂-Edges : Set where e5 : G₂-Edges
data G₂-Nodes : Set where n5 : G₂-Nodes

G₂ : Σ-Algebra Gr
G₂ = record { S = λ { Edge → G₂-Edges ; Node → G₂-Nodes }
            ; F = λ { s → λ { (e5 , ⊤) → n5
                            }
                    ; t → λ { (e5 , ⊤) → n5
                            }
                    }
            }

data F₀-Edges : G₀-Edges → G₁-Edges → Set where
  e0e3 : F₀-Edges e0 e3
  e1e4 : F₀-Edges e1 e4

data F₀-Nodes : G₀-Nodes → G₁-Nodes → Set where
  n0n3 : F₀-Nodes n0 n3
  n1n4 : F₀-Nodes n1 n4
  n2n3 : F₀-Nodes n2 n3

F₀ : Σ-Homorel G₀ G₁
F₀ = record { ρ = λ { {Edge} → F₀-Edges
                    ; {Node} → F₀-Nodes
                    }
            ; ρ-homo = λ { s (.e0 , ⊤) (.e3 , ⊤) (e0e3 , ⊤) → n0n3
                         ; s (.e1 , ⊤) (.e4 , ⊤) (e1e4 , ⊤) → n1n4
                         ; t (.e0 , ⊤) (.e3 , ⊤) (e0e3 , ⊤) → n1n4
                         ; t (.e1 , ⊤) (.e4 , ⊤) (e1e4 , ⊤) → n2n3 }
            }

data F₁-Edges : G₁-Edges → G₂-Edges → Set where
  e3e5₁ : F₁-Edges e3 e5
data F₁-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₁ : F₁-Nodes n3 n5
  n4n5₁ : F₁-Nodes n4 n5

F₁ : Σ-Homorel G₁ G₂
F₁ = record { ρ = λ { {Edge} → F₁-Edges
                    ; {Node} → F₁-Nodes
                    }
            ; ρ-homo = λ { s (.e3 , ⊤) (.e5 , ⊤) (e3e5₁ , ⊤) → n3n5₁
                         ; t (.e3 , ⊤) (.e5 , ⊤) (e3e5₁ , ⊤) → n4n5₁ }
            }

data F₂-Edges : G₁-Edges → G₂-Edges → Set where
  e4e5₂ : F₂-Edges e4 e5
data F₂-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₂ : F₂-Nodes n3 n5
  n4n5₂ : F₂-Nodes n4 n5

F₂ : Σ-Homorel G₁ G₂
F₂ = record { ρ = λ { {Edge} → F₂-Edges
                    ; {Node} → F₂-Nodes
                    }
            ; ρ-homo = λ { s (e4 , ⊤) (e5 , ⊤) (e4e5₂ , ⊤) → n4n5₂
                         ; t (e4 , ⊤) (e5 , ⊤) (e4e5₂ , ⊤) → n3n5₂ }
            }

data F₃-Edges : G₂-Edges → G₂-Edges → Set where
  e5e5 : F₃-Edges e5 e5
data F₃-Nodes : G₂-Nodes → G₂-Nodes → Set where
  n5n5 : F₃-Nodes n5 n5

F₃ : Σ-Homorel G₂ G₂
F₃ = record { ρ = λ { {Edge} → F₃-Edges
                    ; {Node} → F₃-Nodes
                    }
            ; ρ-homo = λ { s (e5 , ⊤) (e5 , ⊤) (e5e5 , ⊤) → n5n5
                         ; t (e5 , ⊤) (e5 , ⊤) (e5e5 , ⊤) → n5n5 }
            }



data Obj : Set where
  ω₀ ω₁ ω₂ : Obj

data _⇒_ : Obj → Obj → Set where
  f₀    : ω₀ ⇒ ω₁
  f₁ f₂ : ω₁ ⇒ ω₂
  f₃    : ω₂ ⇒ ω₂

d : Obj → Σ-Algebra Gr
d ω₀ = G₀
d ω₁ = G₁
d ω₂ = G₂

𝑓₁ : ∀ {A B} → A ⇒ B → Σ-Homorel (d A) (d B)
𝑓₁ f₀ = F₀
𝑓₁ f₁ = F₁
𝑓₁ f₂ = F₂
𝑓₁ f₃ = F₃

data _⇝_[_] : (w₁ w₂ : Obj) → Σ-Homorel (d w₁) (d w₂) → Set where
  A₀ : ω₀ ⇝ ω₁ [ F₀ ]
  A₁ : ω₁ ⇝ ω₂ [ F₁ ]
  A₂ : ω₁ ⇝ ω₂ [ F₂ ]
  A₃ : ω₂ ⇝ ω₂ [ F₃ ]

𝔐 : CounterpartModel Gr
𝔐 = record { W = Obj
           ; d = d
           ; _⇝_ = _⇒_
           ; Σ[_] = 𝑓₁
           }

----------------------------------------------------------------------------------------------------------------------------------------

ℑ : CounterpartWModel Gr
ℑ = CategorifyModel 𝔐

open CounterpartWModel ℑ

T : TemporalStructure W
T = TStructure λ { ω₀ → -, (-, f₀ *)             ∷ []
                 ; ω₁ → -, (-, f₁ *) ∷ (-, f₂ *) ∷ []
                 ; ω₂ → -, (-, f₃ *)             ∷ []
                 }

import LTL

open LTL ℑ T

open SortedAlgebra.Terms Gr

present : ∀ {τ} → [ -, τ ∷ [] ]
present {τ} = ∃< τ > # suc zero ≡ᵗ # zero

notPresent : ∀ {τ} → [ -, τ ∷ [] ]
notPresent {τ} = ∀< τ > # suc zero ≢ᵗ # zero

loop : [ -, Edge ∷ [] ]
loop = s $ (# zero , ⊤) ≡ᵗ t $ (# zero , ⊤)

nextStepPreserved : ∀ {τ} → [ -, τ ∷ [] ]
nextStepPreserved = present ∧ ◯ present

nextStepDeallocated : ∀ {τ} → [ -, τ ∷ [] ]
nextStepDeallocated = present ∧ ◯ notPresent

ExampleLoop : Dec (ω₂ ∋ e5 , ⊤ ⊨ loop)
ExampleLoop = yes (⊨≡ refl)

ExampleExistsNext : ∀ ω n → Dec (ω ∋ n , ⊤ ⊨ ∃< Node > ((# suc zero ≢ᵗ # zero) ∧ (◯ # suc zero ≡ᵗ # zero)))
ExampleExistsNext ω₀ n0 = yes (⊨∃ (n2 ,
                          (⊨∧ (⊨≢ (λ ()) ,
                              ⊨◯ ((-, (((-, refl , n2n3) , (-, refl , n0n3) , ⊤)) , ⊨≡ refl)
                               , ⊤)))))
ExampleExistsNext ω₀ n1 = no λ { (⊨∃ (p ,
                                     ⊨∧ (⊨≢ x ,
                                       ⊨◯ (((n3 , n3 , ⊤) , ((n3 , refl , _   ) , (n4 , ()   , n1n4) , ⊤) , ⊨≡ refl) , ⊤))))
                               ; (⊨∃ (n1 ,
                                     ⊨∧ (⊨≢ x ,
                                       ⊨◯ (((n4 , n4 , ⊤) , ((n4 , refl , n1n4) , (n4 , refl , n1n4) , ⊤) , ⊨≡ refl) , ⊤)))) → x refl }
ExampleExistsNext ω₀ n2 = yes (⊨∃ (n0 ,
                         (⊨∧ (⊨≢ (λ ()) ,
                             ⊨◯ ((-, (((-, refl , n0n3) , (-, refl , n2n3) , ⊤)) , ⊨≡ refl)
                               , ⊤)))))
ExampleExistsNext ω₁ n3 = yes (⊨∃ (n4 ,
                         (⊨∧ ( ⊨≢ (λ ()) ,
                             ⊨◯ ((-, (((-, refl , n4n5₁) , (-, refl , n3n5₁) , ⊤) , ⊨≡ refl))
                               , (-, (((-, refl , n4n5₂) , (-, refl , n3n5₂) , ⊤) , ⊨≡ refl))
                               , ⊤)))))
ExampleExistsNext ω₁ n4 = yes (⊨∃ (n3 ,
                         (⊨∧ ( ⊨≢ (λ ()) ,
                             ⊨◯ ((-, (((-, refl , n3n5₁) , (-, refl , n4n5₁) , ⊤) , ⊨≡ refl))
                               , (-, (((-, refl , n3n5₂) , (-, refl , n4n5₂) , ⊤) , ⊨≡ refl))
                               , ⊤)))))
ExampleExistsNext ω₂ n5 = no λ { (⊨∃ (n5 ,
                            ⊨∧ (⊨≢ x ,
                              ⊨◯ (((n5 , n5 , ⊤) , ((n5 , refl , n5n5) , (n5 , refl , n5n5) , ⊤) , ⊨≡ refl) , ⊤)))) → x refl }

NextStepPreserved : ∀ ω e → Dec (ω ∋ e , ⊤ ⊨ nextStepPreserved {Edge})
NextStepPreserved ω₀ e0 = yes (⊨∧ ((⊨∃ (e0 , (⊨≡ refl)))
                                     , (⊨◯ (((e3 , ⊤) , (((e3 , refl , e0e3) , ⊤) , ⊨∃ (e3 , (⊨≡ refl)))) , ⊤))))
NextStepPreserved ω₀ e1 = yes (⊨∧ ((⊨∃ (e1 , (⊨≡ refl)))
                                     , (⊨◯ (((e4 , ⊤) , ((e4 , (refl , e1e4)) , ⊤) , (⊨∃ (e4 , ⊨≡ refl))) , ⊤))))
NextStepPreserved ω₀ e2 = no λ { (⊨∧ (⊨∃ _ , ⊨◯ ())) }
NextStepPreserved ω₁ e3 = no λ { (⊨∧ (⊨∃ _ , ⊨◯ ())) }
NextStepPreserved ω₁ e4 = no λ { (⊨∧ (⊨∃ _ , ⊨◯ ())) }
NextStepPreserved ω₂ e5 = yes (⊨∧ (⊨∃ (e5 , (⊨≡ refl))
                                     , ⊨◯ (((e5 , ⊤) , (((e5 , (refl , e5e5)) , ⊤) , (⊨∃ (e5 , (⊨≡ refl))))) , ⊤)))

open RelPresheaf⇒

⊨≢-inversion : ∀ {n} {Γ : Vec _ n} {ω τ i} {s : ⟦ Γ ⟧*₀ ω} {t₁ t₂ : (n , Γ) ⊢ τ ⟨ i ⟩}
             → ω ∋ s ⊨ (t₁ ≢ᵗ t₂)
             → η (⟦ t₁ ⟧ᵗ) {ω} s ≢ η (⟦ t₂ ⟧ᵗ) {ω} s
⊨≢-inversion (⊨≢ x) = x

NextStepDeallocated : ∀ ω e → Dec (ω ∋ e , ⊤ ⊨ nextStepDeallocated {Edge})
NextStepDeallocated ω₀ e0 = no λ { (⊨∧ (⊨∃ (e0 , ⊨≡ refl) , ⊨◯ (((e3 , ⊤) , ((e3 , refl , e0e3) , ⊤) , ⊨∀ x) , ⊤))) → ⊨≢-inversion (x e3) refl }
NextStepDeallocated ω₀ e1 = no λ { (⊨∧ (⊨∃ (e1 , ⊨≡ refl) , ⊨◯ (((e4 , ⊤) , ((e4 , refl , e1e4) , ⊤) , ⊨∀ x) , ⊤))) → ⊨≢-inversion (x e4) refl }
NextStepDeallocated ω₀ e2 =
                            --yes (⊨∧ ((⊨∃ (e2 , (⊨≡ refl)))
                            --          , (⊨◯ (((e3 , ⊤)
                            --                   , (((e3 , (refl , {!   !})) , ⊤)
                            --                   , (⊨∀ λ { e3 → ⊨≢ (λ x → {!   !})
                            --                           ; e4 → ⊨≢ (λ x → {!   !}) }))) , ⊤))))

                            --no λ { (LTL.⊨∧ (LTL.⊨∃ _ , LTL.⊨◯ (((a , ⊤) , ((b , r , ()) , ⊤) , LTL.⊨∀ x) , ⊤))) }
                            no λ { (LTL.⊨∧ (LTL.⊨∃ _ , LTL.⊨◯ a)) → {!   !} }
                            -- no λ { (LTL.⊨∧ (LTL.⊨∃ _ , LTL.⊨◯ ())) }

NextStepDeallocated ω₁ e3 = no λ { (LTL.⊨∧ (LTL.⊨∃ _ , LTL.⊨◯ ())) }
NextStepDeallocated ω₁ e4 = no λ { (LTL.⊨∧ (LTL.⊨∃ _ , LTL.⊨◯ ())) }
NextStepDeallocated ω₂ e5 = no λ { (⊨∧ (⊨∃ (e5 , ⊨≡ refl) , ⊨◯ (((e5 , ⊤) , ((e5 , refl , e5e5) , ⊤) , ⊨∀ x) , ⊤))) → ⊨≢-inversion (x e5) refl }
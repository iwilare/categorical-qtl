open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

⟨_,_⟩ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {a b : A} {c d : B} → a ≡ b → c ≡ d → (a , c) ≡ (b , d)
⟨ refl , refl ⟩ = refl

⟨_,_⟩≅ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {D : Set ℓ‴} {a : A} {b : B} {c : C} {d : D} → a ≅ b → c ≅ d → (a , c) ≅ (b , d)
⟨ refl , refl ⟩≅ = refl
open import Data.Vec.Functional using (Vector; head; tail)
open import Data.Fin
open import Data.Nat
open import Data.Maybe using (Maybe)
open import Level renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality

DVector : ∀ {ℓ} (n : ℕ) → (Fin n → Set ℓ) → Set ℓ
DVector n f = ∀ (i : Fin n) → f i

map : ∀ {n} {f g : Fin n → Set} → (∀ {i} → f i → g i) → DVector n f → DVector n g
map = _∘_

dmap : ∀ {n ℓ} {A : Set ℓ} → (A → Set ℓ) → Vector A n → Set ℓ
dmap {n} f v = ∀ (i : Fin n) → (f ∘ v) i
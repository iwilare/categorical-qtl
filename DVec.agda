open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Functional using () renaming (Vector to Assoc)
open import Data.Nat
open import Data.Maybe using (Maybe)
open import Data.Fin using (Fin)
open import Level using (lift) renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Unit using (tt)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality


dvec : ∀ n {ℓ} → Vec Set n → Set ℓ
dvec _ []      = ⊤
dvec _ (x ∷ v) = x × dvec _ v

dmap : ∀ {n ℓ} {A : Set ℓ} → (A → Set ℓ) → Vec A n → Set ℓ
dmap f []      = ⊤
dmap f (x ∷ v) = f x × dmap f v

dzip : ∀ {n ℓ} {A B : Set ℓ} → (A → B → Set ℓ) → Vec A n → Vec B n → Set ℓ
dzip f [] [] = ⊤
dzip f (x ∷ v) (x′ ∷ v′) = f x x′ × dzip f v v′

map : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {f g : A → Set ℓ} → (∀ {i} → f i → g i) → dmap f v → dmap g v
map {v = []}    ρ (lift tt) = lift tt
map {v = _ ∷ _} ρ (x , v)   = ρ x , map ρ v

zip : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {f g : A → Set ℓ} → (∀ {i} → f i → g i → Set ℓ) → dmap f v → dmap g v → Set ℓ
zip {v = []}    ρ (lift tt) (lift tt) = ⊤
zip {v = _ ∷ _} ρ (x , v)   (x′ , v′)  = ρ x x′ × zip ρ v v′



DAssoc : ∀ {ℓ} (n : ℕ) → (Fin n → Set ℓ) → Set ℓ
DAssoc n f = ∀ (i : Fin n) → f i

amap : ∀ {n} {f g : Fin n → Set} → (∀ {i} → f i → g i) → DAssoc n f → DAssoc n g
amap = _∘_

azip : ∀ {n ℓ} {f g : Fin n → Set} → (∀ {i} → f i → g i → Set ℓ) → DAssoc n f → DAssoc n g → Set ℓ
azip {n} f v v′ = ∀ (i : Fin n) → f (v i) (v′ i)

adzip : ∀ {n ℓ} {A B : Set ℓ} → (A → B → Set ℓ) → Assoc A n → Assoc B n → Set ℓ
adzip {n} f v v′ = ∀ (i : Fin n) → f (v i) (v′ i)

admap : ∀ {n ℓ} {A : Set ℓ} → (A → Set ℓ) → Assoc A n → Set ℓ
admap {n} f v = ∀ (i : Fin n) → (f ∘ v) i
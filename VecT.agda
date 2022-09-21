module VecT where

import Data.Unit
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Function using (id; _∘_; flip)
open import Level using (Level; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

pattern * = lift Data.Unit.tt

private
  variable
    n : ℕ
    ℓ ℓ′ : Level
    A B : Set ℓ
    f g : A → Set ℓ
    v : Vec A n

mapT : (A → Set ℓ) → Vec A n → Set ℓ
mapT f [] = ⊤
mapT f (x ∷ xs) = f x × mapT f xs

zipT : (A → B → Set ℓ) → Vec A n → Vec B n → Set ℓ
zipT R [] [] =  ⊤
zipT R (x ∷ xs) (y ∷ ys) = R x y × zipT R xs ys

map : (∀ {x} → f x → g x)
    → mapT f v → mapT g v
map {v = []} p * = *
map {v = _ ∷ _} p (x , xs) = p x , map p xs

zip : (∀ {x} → f x → g x → Set ℓ′)
    → mapT f v → mapT g v → Set ℓ′
zip {v = []} p * * = ⊤
zip {v = _ ∷ _} p (x , xs) (y , ys) = p x y × zip p xs ys

lookup : (i : Fin n)
        → mapT f v
        → f (Vec.lookup v i)
lookup {v = _ ∷ _} zero (x , xs) = x
lookup {v = _ ∷ _} (suc i) (x , xs) = lookup i xs

lookup-zip : ∀ {f g : A → Set ℓ} {v : Vec A n} {x : mapT f v} {y : mapT g v} {ρ : ∀ {x} → f x → g x → Set ℓ}
          → (i : Fin n)
          → zip ρ x y
          → ρ (lookup i x) (lookup i y)
lookup-zip {v = _ ∷ _} zero (x , xs) = x
lookup-zip {v = _ ∷ _} (suc i) (x , xs) = lookup-zip i xs

zip-imply : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {f g : (A → Set ℓ′)} {x : mapT f v} {y : mapT g v} {p r : (∀ {x} → f x → g x → Set ℓ′)}
      → (∀ {m} {x y} → p {m} x y → r {m} x y)
      → zip p x y
      → zip r x y
zip-imply {v = []} η * = *
zip-imply {v = _ ∷ _} η (x , xs) = η x , zip-imply η xs

zip-ext : ∀ {v : Vec A n} {f : (A → Set ℓ)} {x y : mapT f v}
        → zip _≡_ x y
        → x ≡ y
zip-ext {v = []} {x = *} {y = *} * = refl
zip-ext {v = _ ∷ _} {x = _ , _} {y = _ , _} (refl , x) rewrite zip-ext x = refl

zip-id : ∀ {v : Vec A n} {f : (A → Set ℓ)} {x : mapT f v}
        → zip _≡_ x x
zip-id {v = []} {x = *} = *
zip-id {v = _ ∷ _} {x = _ , xs} = refl , zip-id {x = xs}

map-cong : ∀ {v : Vec A n} {f g : A → Set ℓ} {x : mapT f v} {f g : (∀ {x} → f x → g x)}
          → (e : ∀ {x} σ → f {x} σ ≡ g {x} σ)
          → map f x ≡ map g x
map-cong {v = []} e = refl
map-cong {v = _ ∷ _} {x = x , xs} e rewrite e x | map-cong {x = xs} e = refl

map-comp : ∀ {v : Vec A n} {i j k : A → Set ℓ} {x : mapT i v} {f : (∀ {x} → j x → k x)} {g : (∀ {x} → i x → j x)}
          → map (f ∘ g) x ≡ map f (map g x)
map-comp {v = []} = refl
map-comp {v = _ ∷ _} {x = _ , xs} {f = f} {g = g} rewrite map-comp {x = xs} {f = f} {g = g} = refl

map-id : ∀ {v : Vec A n} {f : A → Set ℓ} {x : mapT f v}
        → map id x ≡ x
map-id {v = []} = refl
map-id {v = _ ∷ _} {x = _ , xs} rewrite map-id {x = xs} = refl

zip-rel-decomp : ∀ {v : Vec A n} {f g h : (A → Set ℓ)} {x : mapT g v} {y : mapT h v}
        → {p : (∀ {x} → g x → f x → Set ℓ)}
        → {r : (∀ {x} → f x → h x → Set ℓ)}
        → zip (λ x y → ∃[ a ] (p x a × r a y)) x y
        → Σ[ a ∈ mapT f v ] (zip p x a × zip r a y)
zip-rel-decomp {v = []} * = * , * , *
zip-rel-decomp {v = _ ∷ _} (x , xs) with zip-rel-decomp xs | x
... | f , g , h | a , x , y = (a , f) , (x , g) , (y , h)

zip-rel-comp : ∀ {v : Vec A n} {f g h : (A → Set ℓ)} {a : mapT f v} {x : mapT g v} {y : mapT h v}
        → {s : (∀ {x} → g x → f x → Set ℓ)}
        → {t : (∀ {x} → f x → h x → Set ℓ)}
        → zip s x a → zip t a y
        → zip (λ x y → ∃[ a ] (s x a × t a y)) x y
zip-rel-comp {v = []} * * = *
zip-rel-comp {v = _ ∷ _} (x , xs) (y , ys) = (_ , x , y) , zip-rel-comp xs ys

op : ∀ {v : Vec A n} {f g : (A → Set ℓ)} {x : mapT f v} {y : mapT g v}
    → {f : (∀ {x} → f x → g x → Set ℓ′)}
    → zip f        x y
    → zip (flip f) y x
op {v = []} * = *
op {v = _ ∷ _} (x , xs) = x , op xs 
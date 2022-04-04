module DVec where

open import Data.Vec as V using ([]; _∷_) renaming (Vec to Vector)

open import Data.Maybe using (Maybe)
open import Data.Fin using (Fin; zero)
open import Level using (lift) renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Unit using (tt)
open import Function using (_∘_; const; id)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

dassoc : ∀ {n ℓ} → Vector (Set ℓ) n → Set ℓ
dassoc []      = ⊤
dassoc (x ∷ v) = x × dassoc v

map : ∀ {n ℓ} {A : Set ℓ} → (A → Set ℓ) → Vector A n → Set ℓ
map f []      = ⊤
map f (x ∷ v) = f x × map f v

amap : ∀ {n ℓ} {A : Set ℓ} → (A → Set ℓ) → Vector A n → Set ℓ
amap f v = dassoc (V.map f v)

zip : ∀ {n ℓ} {A B : Set ℓ} → (A → B → Set ℓ) → Vector A n → Vector B n → Set ℓ
zip f [] []             = ⊤
zip f (x ∷ v) (x′ ∷ v′) = f x x′ × zip f v v′

azip : ∀ {n ℓ} {A B : Set ℓ} → (A → B → Set ℓ) → Vector A n → Vector B n → Set ℓ
azip f v v′ = dassoc (V.zipWith f v v′)

alookup : ∀ {n ℓ} {v : Vector (Set ℓ) n} → (i : Fin n) → dassoc v → V.lookup v i
alookup {v = _ ∷ _} zero (x , v) = x
alookup {v = _ ∷ _} (Fin.suc i) (x , v) = alookup i v

lookup : ∀ {n ℓ} {A : Set ℓ} {v : Vector A n} {f : (A → Set ℓ)} → (i : Fin n) → map f v → f (V.lookup v i)
lookup {v = _ ∷ _} zero (x , v) = x
lookup {v = _ ∷ _} (Fin.suc i) (x , v) = lookup i v

dzip : ∀ {n ℓ} {A : Set ℓ} {v : Vector A n} {f g : (A → Set ℓ)} → (∀ {x} → f x → g x → Set ℓ) → map f v → map g v → Set ℓ
dzip {v = []} a (lift tt) (lift tt) = ⊤
dzip {v = _ ∷ _} a (x , v) (x′ , v′) = a x x′ × dzip a v v′

ziplookup : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {f g : (A → Set ℓ)} {v : map f o} {v′ : map g o} {ρ : ∀ {x} → f x → g x → Set ℓ} → (i : Fin n) → dzip ρ v v′ → ρ (lookup i v) (lookup i v′)
ziplookup {o = _ ∷ _} zero        (x , v) = x
ziplookup {o = _ ∷ _} (Fin.suc i) (x , v) = ziplookup i v

dmap : ∀ {n ℓ} {A : Set ℓ} {v : Vector A n} {f g : (A → Set ℓ)} → (∀ {x} → f x → g x) → map f v → map g v
dmap {v = []}    a (lift tt) = lift tt
dmap {v = _ ∷ _} a (x , v)   = a x , dmap a v

ddzip : ∀ {n ℓ} {A : Set ℓ} {vo : Vector A n} {vf vg : (A → Set ℓ)} {v : map vf vo} {v′ : map vg vo}
      → {f g : (∀ {x} → vf x → vg x → Set ℓ)}
      → (∀ {m} {x y} → f {m} x y → g {m} x y)
      → dzip f v v′
      → dzip g v v′
ddzip {vo = []} e (lift tt) = lift tt
ddzip {vo = _ ∷ _} e (x , v) = e x , ddzip e v

zipext : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {f : (A → Set ℓ)} {v v′ : map f o}
       → dzip _≡_ v v′
       → v ≡ v′
zipext {o = []} {v = lift tt} {lift tt} (lift tt) = P.refl
zipext {o = _ ∷ _} {v = x , v} {v′ = .x , v′} (P.refl , snd) rewrite zipext snd = P.refl

dzipid : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {f : (A → Set ℓ)} {v : map f o}
       → dzip _≡_ v v
dzipid {o = []} {v = lift tt} = lift tt
dzipid {o = _ ∷ _} {v = _ , v} = P.refl , dzipid {v = v}

dextf : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {f g : A → Set ℓ} {v : map f o}
      → {f g : (∀ {x} → f x → g x)}
      → (e : ∀ {x} σ → f {x} σ ≡ g {x} σ)
      → dmap f v ≡ dmap g v
dextf {o = []} e = P.refl
dextf {o = _ ∷ o} {v = x , v} e rewrite e x | dextf {o = o} {v = v} e = P.refl

dcomp : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {i j k : A → Set ℓ} {v : map i o}
      → {f : (∀ {x} → j x → k x)}
      → {g : (∀ {x} → i x → j x)}
      → dmap (f ∘ g) v ≡ dmap f (dmap g v)
dcomp {o = []} = P.refl
dcomp {o = x ∷ o} {v = _ , v} {f = f} {g = g} rewrite dcomp {v = v} {f = f} {g = g} = P.refl

did : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {f : A → Set ℓ} {v : map f o}
    → dmap id v ≡ v
did {o = []} = P.refl
did {o = _ ∷ _} {v = _ , v} rewrite did {v = v}= P.refl

zipcomp : ∀ {n ℓ} {A : Set ℓ} {vo : Vector A n} {va vx vy : (A → Set ℓ)} {a : map va vo} {x : map vx vo} {y : map vy vo}
        → {f : (∀ {x} → vx x → va x → Set ℓ)}
        → {g : (∀ {x} → va x → vy x → Set ℓ)}
        → {z : (∀ {x} → vx x → vy x → Set ℓ)}
        → (e : (∀ {σ} {x y a} → f {σ} x a → g {σ} a y → z {σ} x y))
        → dzip f x a
        → dzip g a y
        → dzip z x y
zipcomp {vo = []} e (lift tt) (lift tt) = lift tt
zipcomp {vo = _ ∷ _} e (x , v) (x′ , v′) = e x x′ , zipcomp e v v′

zipdecomp : ∀ {n ℓ} {A : Set ℓ} {vo : Vector A n} {va vx vy : (A → Set ℓ)} {x : map vx vo} {y : map vy vo}
        → {f : (∀ {x} → vx x → va x → Set ℓ)}
        → {g : (∀ {x} → va x → vy x → Set ℓ)}
        → {z : (∀ {x} → vx x → vy x → Set ℓ)}
        → (e : (∀ {σ} {x y} → z {σ} x y → Σ[ a ∈ va σ ] (f {σ} x a × g {σ} a y)))
        → dzip z x y
        → Σ[ a ∈ map va vo ] (dzip f x a × dzip g a y)
zipdecomp {vo = []} e (lift tt) = lift tt , lift tt , lift tt
zipdecomp {vo = _ ∷ _} e (x , v) with zipdecomp e v | e x
... | va , vx , vy | a , x , y = (a , va) , (x , vx) , (y , vy)
module DVec where

open import Data.Vec using (Vec; _∷_; []; lookup)

open import Data.Nat
open import Data.Maybe using (Maybe)
open import Data.Fin using (Fin)
open import Level using (lift) renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Unit using (tt)
open import Function using (_∘_; const; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

dvec : ∀ {n ℓ} → Vec (Set ℓ) n → Set ℓ
dvec []      = ⊤
dvec (x ∷ v) = x × dvec v

map : ∀ {n ℓ} {A : Set ℓ} → (A → Set ℓ) → Vec A n → Set ℓ
map f []      = ⊤
map f (x ∷ v) = f x × map f v

dmap : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {f g : A → Set ℓ} → (∀ {i} → f i → g i) → map f v → map g v
dmap {v = []}    ρ (lift tt) = lift tt
dmap {v = _ ∷ _} ρ (x , v)   = ρ x , dmap ρ v

dzip : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {f g : A → Set ℓ} → (∀ {i} → f i → g i → Set ℓ) → map f v → map g v → Set ℓ
dzip {v = []}    ρ (lift tt) (lift tt) = ⊤
dzip {v = _ ∷ _} ρ (x , v)   (x′ , v′)  = ρ x x′ × dzip ρ v v′

--Bisim : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} (x : map a v) → (y : map b v) → Set ℓ
--Bisim {v = []} (lift tt) (lift tt) = ⊤
--Bisim {v = _ ∷ _} (x , v) (x′ , v′) = x ≅ x′ × Bisim v v′
--
--bello : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} (x : map a v) → (y : map b v) → Set ℓ
--bello {v = []} (lift tt) (lift tt) = ⊤
--bello {v = _ ∷ _} (x , v) (x′ , v′) = x ≅ x′ × bello v v′



DExtId : ∀ {n ℓ} {A : Set ℓ} {a : A → Set ℓ} {v : Vec A n} {f : ∀ {i : A} → a i → a i} → (∀ {i} (x : a i) → f x ≡ x) → (x : map a v) → dmap f x ≡ x
DExtId {v = []} e (lift tt) = refl
DExtId {v = _ ∷ _} {f} e (x , v) rewrite e x | DExtId {f = f} e v = refl

DExtt : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} {f g : ∀ {i : A} → a i → b i} → (∀ {i} (x : a i) (y : a i) → f x ≡ g y) → (x : map a v) → (y : map a v) → dmap f x ≡ dmap g y
DExtt {v = []} e (lift tt) (lift tt) = refl
DExtt {v = _ ∷ _} {f} {g} e (x , v) (x′ , v′) rewrite e x x′ | DExtt {f = f} {g} e v v′ = refl


DAssociative : ∀ {n ℓ} {A : Set ℓ} {v : Vec A n} {a b c : A → Set ℓ} {f : ∀ {i : A} → a i → b i} {g : ∀ {i : A} → b i → c i} → (x : map a v) → dmap g (dmap f x) ≡ dmap (g ∘ f) x
DAssociative {v = []} (lift tt)  = refl
DAssociative {v = _ ∷ _} {f = f} {g = g} (x , v) rewrite DAssociative {f = f} {g = g} v = refl


--
--DB : ∀ {n ℓ} {A B : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} {f g : map a v → B} → (x : map a v) → f x ≡ g x
--DB {v = []} (lift tt) = {!   !}
--DB {v = _ ∷ _} (x , v) = {!   !}

--
--bisim : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} (x : map a v) → (y : map b v) → Bisim x y → x ≅ y
--bisim {v = []} (lift tt) (lift tt) (lift tt) = refl
--bisim {v = _ ∷ _} (x , v) (x′ , v′) (e , ev) rewrite ≅-to-≡ e = {!   !}

--DGrop : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} (x : map a v) → (y : map b v) → (e : ∀ i → lookup a i ≡ lookup b i) → x ≅ y
--DGrop {v = []}    e (lift tt) (lift tt) = refl
--DGrop {v = t ∷ _} e (x , v) (x′ , v′) = {!   !}

-- DGrop e v v′
-- ... | H.refl = {! rr !}


{-
DExt : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} {f g : ∀ {i : A} → a i → b i} → (∀ {i} (x : a i) → f x ≡ g x) → (x : dmap a v) → map f x ≡ map g x
DExt {v = []} e (lift tt) = P.refl
DExt {v = _ ∷ _} {f} {g} e (x , v) rewrite e x | DExt {f = f} {g} e v = P.refl

--DExtt : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} {f g : ∀ {i : A} → a i → b i} → (∀ {i} (x : a i) → f x ≡ g x) → (x : dmap a v) → map f x ≡ x
--DExtt {v = []} e (lift tt) = ?
--DExtt {v = _ ∷ _} {f} {g} e (x , v) rewrite e x | DExtt {f = f} {g} e v = ?

--DGrop : ∀ {n ℓ} {A : Set ℓ} {a b : A → Set ℓ} {v : Vec A n} {f g : ∀ {i : A} → a i → b i} → (e : ∀ {i} (𝒶 : a i) (𝓫 : b i) → f 𝒶 ≅ g 𝓫) → (x : dmap a v) → (y : dmap b v) → x ≅ y
--DGrop {v = []}    e (lift tt) (lift tt) = refl
--DGrop {v = _ ∷ _} e (x , v) (x′ , v′) = ⟨ ? , DGrop e v v′ ⟩≅
-}
open import Prelude
open import Prelude.ListProperties
    using (length-map; length-++; ∷-inj)
open import Prelude.NatProperties
     using (+-comm; suc-inj; +-inj-1; +-inj-2)

module Prelude.Vector where

  open import Data.Vec 
    using (Vec; []; _∷_; head; tail; lookup; tabulate) 
    renaming (_++_ to _++v_)
    public

  data All {a b}{A : Set a}(P : A → Set b) : {n : ℕ} → Vec A n → Set (a ⊔ b) where
    []  : All P []
    _∷_ : {n : ℕ}{k : A}{v : Vec A n}
        → P k → All P v → All P (k ∷ v)

  data VecI {a b}{A : Set a}(F : A → Set b) : {n : ℕ} → Vec A n → Set (a ⊔ b) where
    []  : VecI F []
    _∷_ : {n : ℕ}{K : A}{V : Vec A n}
        → F K → VecI F V → VecI F (K ∷ V)

  lookupᵢ : ∀{a b}{A : Set a}{F : A → Set b}{n : ℕ}{v : Vec A n}
          → (i : Fin n) → VecI F v → F (lookup i v)
  lookupᵢ fz (x ∷ vs) = x
  lookupᵢ (fs i) (x ∷ vs) = lookupᵢ i vs

  ∷ᵥ-inj : {n : ℕ}{A : Set}{v u : A}{vs us : Vec A n}
         → _≡_ {A = Vec A (suc n)}(v ∷ vs) (u ∷ us)
         → v ≡ u × vs ≡ us
  ∷ᵥ-inj refl = refl , refl

  swap : {A : Set}{n : ℕ} → Fin n → Vec A n → A → Vec A n
  swap () [] a
  swap fz     (v ∷ vs) a = a ∷ vs
  swap (fs i) (v ∷ vs) a = v ∷ (swap i vs a)

  swap-uni
    : {A : Set}{n : ℕ}(i : Fin n)(v : Vec A n)
    → swap i v (lookup i v) ≡ v
  swap-uni () []
  swap-uni fz (x ∷ v) = refl
  swap-uni (fs i) (x ∷ v) = cong (x ∷_) (swap-uni i v)

  vsum : {k : ℕ} → Vec ℕ k → ℕ
  vsum [] = 0
  vsum (x ∷ xs) = x + vsum xs

  vec : {k : ℕ}{A : Set}(l : List A)
      → length l ≡ k → Vec A k
  vec []       refl = []
  vec {zero}  (x ∷ xs) ()
  vec {suc k} (x ∷ xs) p = x ∷ vec xs (suc-inj p)

  toList : {k : ℕ}{A : Set}(v : Vec A k)
         → List A
  toList []      = []
  toList (x ∷ v) = x ∷ toList v

  length-toList : {k : ℕ}{A : Set}(v : Vec A k)
                → length (toList v) ≡ k
  length-toList [] = refl
  length-toList (x ∷ v) = cong suc (length-toList v)

  vec-reduce : {k : ℕ}{A : Set}(l : List A){p q : length l ≡ k}
             → vec l p ≡ vec l q
  vec-reduce l {refl} {refl} = refl

  vec-reindx : {k m : ℕ}{A : Set}(p : k ≡ m)
             → Vec A k → Vec A m
  vec-reindx refl v = v

  vec-reindx-uni
    : {k m : ℕ}{A : Set}(p : k ≡ m)
    → (v : Vec A m)
    → vec-reindx p (vec-reindx (sym p) v) ≡ v
  vec-reindx-uni refl v = refl

  vec-reindx-elim
    : {k m : ℕ}{A : Set}{P : {l : ℕ} → Vec A l → Set}
    → (p : k ≡ m)(v : Vec A k)
    → P (vec-reindx p v)
    → P v
  vec-reindx-elim refl v pv = pv
    

  vec-toList : {k : ℕ}{A : Set}(v : Vec A k)
             → vec (toList v) (length-toList v) ≡ v
  vec-toList [] = refl
  vec-toList (x ∷ v) 
    = cong (_∷_ x) (trans (vec-reduce (toList v)) (vec-toList v))

  toList-vec : {k : ℕ}{A : Set}(l : List A){p : length l ≡ k}
             → toList (vec l p) ≡ l
  toList-vec [] {refl} = refl
  toList-vec (x ∷ l) {refl} = cong (_∷_ x) (toList-vec l)

  toList-vec-≡ : {A : Set}(l : List A)
               → (v : Vec A (length l))
               → toList v ≡ l
               → v ≡ vec l refl
  toList-vec-≡ [] [] hip = refl
  toList-vec-≡ (x ∷ l) (x₁ ∷ v) hip 
    = cong₂ _∷_ (p1 (∷-inj hip)) (toList-vec-≡ l v (p2 (∷-inj hip)))

  vec-≡ : {k : ℕ}{A : Set}{l₁ l₂ : List A}
          {p : length l₁ ≡ k}{q : length l₂ ≡ k}
        → l₁ ≡ l₂ → vec l₁ p ≡ vec l₂ q
  vec-≡ {l₁ = l} refl = vec-reduce l

  vmap : ∀{a}{k : ℕ}{A B : Set a}(f : A → B)
       → Vec A k → Vec B k
  vmap f []       = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

  vmapM : {k : ℕ}{A B : Set}(f : A → Maybe B)
       → Vec A k → Maybe (Vec B k)
  vmapM f []       = just []
  vmapM f (x ∷ xs) = _∷_ <M> f x <M*> vmapM f xs

  vmap-vec : {k : ℕ}{A B : Set}(f : A → B)(l : List A)
             {p : length l ≡ k}{q : length (map f l) ≡ k}
           → vmap f (vec l p) ≡ vec (map f l) q
  vmap-vec f []      {refl} {refl} = refl
  vmap-vec f (x ∷ l) {refl} {q}
    = cong (_∷_ (f x)) (trans (vmap-vec f l {q = suc-inj q}) 
                              (vec-reduce (map f l)))

  toList-vmap : {k : ℕ}{A B : Set}(f : A → B)(v : Vec A k)
              → toList (vmap f v) ≡ map f (toList v)
  toList-vmap f [] = refl
  toList-vmap f (x ∷ v) = cong (_∷_ (f x)) (toList-vmap f v)

  vmap-lemma
    : {k : ℕ}{A B : Set}{f : A → B}{g : B → A}
    → (v : Vec A k)
    → (∀ x → g (f x) ≡ x)
    → vmap g (vmap f v) ≡ v
  vmap-lemma [] prf      = refl
  vmap-lemma (x ∷ k) prf = cong₂ _∷_ (prf x) (vmap-lemma k prf)

  vmap-id
    : {k : ℕ}{A : Set}(v : Vec A k)
    → vmap id v ≡ v
  vmap-id []       = refl
  vmap-id (x ∷ xs) = cong (_∷_ x) (vmap-id xs)

  vmap-compose
    : {k : ℕ}{A B C : Set}{f : B → C}{g : A → B}
    → (v : Vec A k)
    → vmap f (vmap g v) ≡ vmap (f ∘ g) v
  vmap-compose [] = refl
  vmap-compose {f = f} {g} (x ∷ v) = cong (_∷_ (f (g x))) (vmap-compose v)

  vsplit : {n : ℕ}{A : Set}(m : ℕ) 
         → Vec A (m + n) → Vec A m × Vec A n
  vsplit zero v          = [] , v
  vsplit (suc m) (x ∷ v) = x ∷ p1 (vsplit m v) , p2 (vsplit m v)

  vsplit-elim
    : {m n : ℕ}{A : Set}(l₁ l₂ : List A)
      {p : length (l₁ ++ l₂) ≡ m + n}
      {q₁ : length l₁ ≡ m}{q₂ : length l₂ ≡ n}
    → vsplit m (vec (l₁ ++ l₂) p) ≡ (vec l₁ q₁ , vec l₂ q₂)
  vsplit-elim [] l2 {q₁ = refl} {q₂} 
    = cong (_,_ []) (vec-reduce l2)
  vsplit-elim (x ∷ l1) l2 {q₁ = refl} {q₂} 
    = cong (λ P → x ∷ p1 P , p2 P) (vsplit-elim l1 l2)

  vsplit-ump 
    : {m n : ℕ}{A : Set}(v1 : Vec A m)(v2 : Vec A n)
    → vsplit m (v1 ++v v2) ≡ (v1 , v2)
  vsplit-ump [] v2 = refl
  vsplit-ump (x ∷ v1) v2 
    rewrite vsplit-ump v1 v2 = refl

  vsplit-lemma 
    : {m n : ℕ}{A : Set}(v1 : Vec A m)(v2 : Vec A n)(vres : Vec A (m + n))
    → vsplit m vres ≡ (v1 , v2)
    → vres ≡ (v1 ++v v2)
  vsplit-lemma [] v2 .v2 refl = refl
  vsplit-lemma {suc m} {n} (v ∷ ._) ._ (.v ∷ vres) refl 
    = cong (_∷_ v) (vsplit-lemma (p1 (vsplit m vres)) (p2 (vsplit m vres)) vres refl)

  private
    length-elim-1 
      : {n m : ℕ}{A : Set}(l1 l2 : List A)
      → length l1 ≡ m
      → length (l1 ++ l2) ≡ m + n
      → length l2 ≡ n
    length-elim-1 l1 l2 refl q 
      rewrite length-++ l1 {ys = l2}
           = +-inj-1 {m = length l1} q

    length-elim-2
      : {n m : ℕ}{A : Set}(l1 l2 : List A)
      → length l2 ≡ n
      → length (l1 ++ l2) ≡ m + n
      → length l1 ≡ m
    length-elim-2 l1 l2 refl q 
      rewrite length-++ l1 {ys = l2}
           = +-inj-2 {m = length l2} q

  vsplit-elim-1 
    : {m n : ℕ}{A : Set}(l₁ l₂ : List A)
      {p : length (l₁ ++ l₂) ≡ m + n}
      {q : length l₁ ≡ m}
    → p1 (vsplit m (vec (l₁ ++ l₂) p)) ≡ vec l₁ q
  vsplit-elim-1 l1 l2 {p} {q}
    rewrite vsplit-elim l1 l2 {p} {q} {length-elim-1 l1 l2 q p}
      = refl

  vsplit-elim-2
    : {m n : ℕ}{A : Set}(l₁ l₂ : List A)
      {p : length (l₁ ++ l₂) ≡ m + n}
      {q : length l₂ ≡ n}
    → p2 (vsplit m (vec (l₁ ++ l₂) p)) ≡ vec l₂ q
  vsplit-elim-2 {m} l1 l2 {p} {q}
    rewrite vsplit-elim {m} l1 l2 {p} {length-elim-2 l1 l2 q p} {q}
      = refl

  toList-vsplit-++
    : {m n : ℕ}{A : Set}(as : Vec A (m + n))
    → toList as ≡ toList (p1 (vsplit m as)) ++ toList (p2 (vsplit m as))
  toList-vsplit-++ {zero} as = refl
  toList-vsplit-++ {suc m} (x ∷ as) 
    = cong (_∷_ x) (toList-vsplit-++ {m = m} as)

  map-toList-lemma
    : {m : ℕ}{A B : Set}(as : Vec A m)
    → (f : A → B)
    → map f (toList as) ≡ toList (vmap f as)
  map-toList-lemma [] f = refl
  map-toList-lemma (x ∷ as) f 
    = cong (_∷_ (f x)) (map-toList-lemma as f)

  vzip : {k l : ℕ}{A B : Set}
       → k ≡ l → Vec A k → Vec B l → Vec (A × B) k
  vzip refl [] [] = []
  vzip refl (x ∷ v1) (y ∷ v2)
    = (x , y) ∷ vzip refl v1 v2

  vzip-elim-p1
    : {k l : ℕ}{A B : Set}(vA : Vec A k)(vB : Vec B l)
    → {prf : k ≡ l}
    → vmap p1 (vzip prf vA vB) ≡ vA
  vzip-elim-p1 [] [] {refl} = refl
  vzip-elim-p1 (a ∷ vA) (b ∷ vB) {refl} = cong (_∷_ a) (vzip-elim-p1 vA vB)

  vzip-elim-p2
    : {k : ℕ}{A B : Set}(vA : Vec A k)(vB : Vec B k)
    → vmap p2 (vzip refl vA vB) ≡ vB
  vzip-elim-p2 [] [] = refl
  vzip-elim-p2 (a ∷ vA) (b ∷ vB) = cong (_∷_ b) (vzip-elim-p2 vA vB)

  vsum-spec : {k : ℕ}(v : Vec ℕ k)
            → vsum v ≡ sum (toList v)
  vsum-spec [] = refl
  vsum-spec (x ∷ v) = cong (_+_ x) (vsum-spec v)

  vdrop : {k : ℕ}{A : Set}
        → Vec A (suc k) → Fin (suc k) → Vec A k
  vdrop (x ∷ v) fz = v
  vdrop (x ∷ []) (fs ())
  vdrop (x ∷ x₁ ∷ v) (fs f) = x ∷ vdrop (x₁ ∷ v) f

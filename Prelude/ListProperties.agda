open import Prelude
open import Prelude.NatProperties using (suc-inj; +-comm)
open import Data.List using (drop)

module Prelude.ListProperties where

  open import Data.List.Properties
    using ( length-++; map-compose; map-++-commute
          ; length-map; map-id
          )
    renaming (∷-injective to ∷-inj)
    public

  open import Data.List.All
    using (All; []; _∷_)
    renaming (all to all?)
    public

  open import Data.List.Any
    using (Any; here; there; module Membership-≡)
    public

  open Membership-≡
    public

  ∷≡[]→⊥ : ∀{a}{A : Set a}{x : A}{xs : List A}
         → _≡_ {A = List A} (x ∷ xs) [] → ⊥
  ∷≡[]→⊥ ()

  lsplit-++-lemma
    : ∀{a}{A : Set a}(l1 l2 : List A) 
    → lsplit (length l1) (l1 ++ l2) ≡ (l1 , l2)
  lsplit-++-lemma [] l2 = refl
  lsplit-++-lemma (x ∷ l1) l2 
    rewrite lsplit-++-lemma l1 l2 
          = refl

  lsplit-elim
    : ∀{a}{A : Set a}(k : ℕ)(l : List A){m n : List A}
    → lsplit k l ≡ (m , n)
    → l ≡ m ++ n
  lsplit-elim zero l refl = refl
  lsplit-elim (suc k) [] refl = refl
  lsplit-elim (suc k) (x ∷ l) refl = cong (_∷_ x) (lsplit-elim k l refl)

  length-lemma 
    : {n : ℕ}{A : Set}(l1 l2 : List A)
    → length l1 ≡ n → n ≤ length (l1 ++ l2)
  length-lemma [] l2 refl = z≤n
  length-lemma (x ∷ l1) l2 refl = s≤s (length-lemma l1 l2 refl)

  lsplit-length-≤-lemma
    : ∀{a}{A : Set a}(l : List A)
    → (m n : ℕ)
    → m + n ≤ length l
    → m ≤ length (p1 (lsplit m l))
    × n ≤ length (p2 (lsplit m l))
  lsplit-length-≤-lemma l zero n hip = z≤n , hip
  lsplit-length-≤-lemma [] (suc m) n ()
  lsplit-length-≤-lemma (x ∷ l) (suc m) n (s≤s hip) 
    = let r1 , r2 = lsplit-length-≤-lemma l m n hip
       in (s≤s r1) , r2

  lsplit-length-≡-lemma
    : ∀{a}{A : Set a}(l : List A)
    → (m n : ℕ)
    → (hip : length l ≡ m + n)
    → (length (p1 (lsplit m l)) ≡ m)
    × (length (p2 (lsplit m l)) ≡ n)
  lsplit-length-≡-lemma [] zero .0 refl 
    = refl , refl
  lsplit-length-≡-lemma [] (suc m) n ()
  lsplit-length-≡-lemma (x ∷ l) zero n hip 
    = refl , hip
  lsplit-length-≡-lemma (x ∷ l) (suc m) n hip 
    = let r1 , r2 = lsplit-length-≡-lemma l m n (suc-inj hip)
       in cong suc r1 , r2

  lhead-elim : ∀{a}{A : Set a}{x : A}(l : List A)
             → lhead l ≡ just x
             → l ≡ (x ∷ [])
  lhead-elim [] ()
  lhead-elim (x ∷ []) refl = refl
  lhead-elim (x₁ ∷ x₂ ∷ l) ()

  map-lemma : {A B : Set}{f : A → B}{g : B → A}
            → (l : List A)
            → (∀ x → g (f x) ≡ x)
            → map g (map f l) ≡ l
  map-lemma [] prf      = refl
  map-lemma (x ∷ l) prf = cong₂ _∷_ (prf x) (map-lemma l prf)

  list-split-lemma 
    : {A : Set}{n : ℕ}{l : List A}
    → n ≤ length l
    → Σ (List A × List A)
        (λ ls → length (p1 ls) ≡ n × l ≡ (p1 ls) ++ (p2 ls))
  list-split-lemma {n = zero} {l = l} n≤l 
    = ([] , l) , refl , refl
  list-split-lemma {n = suc n} {[]} ()
  list-split-lemma {n = suc n} {x ∷ l} (s≤s n≤l)
    with list-split-lemma {n = n} {l = l} n≤l
  ...| (la , lb) , pla , plb 
     = ((x ∷ la) , lb) , ((cong suc pla) , (cong (_∷_ x) plb))

  ++-[] : ∀{a}{A : Set a}{l j : List A}
        → l ++ j ≡ []
        → l ≡ [] × j ≡ []
  ++-[] {l = []} prf = refl , prf
  ++-[] {l = x ∷ l} ()

  ++-left-id : ∀{a}{A : Set a}(l : List A)
             → l ++ [] ≡ l
  ++-left-id []       = refl
  ++-left-id (l ∷ ls) = cong (_∷_ l) (++-left-id ls)

  ++-length : ∀{a}{A : Set a}{l1 l2 : List A}{n1 n2 : ℕ}
            → length l1 ≡ n1
            → length l2 ≡ n2
            → length (l1 ++ l2) ≡ n1 + n2
  ++-length {l1 = l1} {l2 = l2} p1 p2 
    rewrite length-++ l1 {ys = l2} = cong₂ _+_ p1 p2

  length-++-stable : {A : Set}{l j : List A}{n : ℕ}
                   → length (l ++ j) ≡ length l + n
                   → length j ≡ n
  length-++-stable {l = []} prf = prf
  length-++-stable {l = x ∷ l} {j} prf  
    = length-++-stable {l = l} {j} (suc-inj prf)

  length-≤ : {A : Set}{j : List A}
           → (l : List A)
           → length l ≤ length (l ++ j)
  length-≤ [] = z≤n
  length-≤ (_ ∷ l) = s≤s (length-≤ l)

  drop[]≡[] : {A : Set}{n : ℕ} → drop {A = A} n [] ≡ []
  drop[]≡[] {n = zero} = refl
  drop[]≡[] {n = suc n} = refl
  
  drop-+-comm
    : {A : Set}{l : List A}(n m : ℕ) → drop (n + m) l ≡ drop n (drop m l)
  drop-+-comm zero m = refl
  drop-+-comm {A} {l = []} (suc n) m with drop[]≡[] {A} {m}
  ...| r rewrite r = refl
  drop-+-comm {l = x ∷ l} (suc n) zero 
    rewrite (+-comm n zero) = refl
  drop-+-comm {l = x ∷ l} (suc n) (suc m) with drop-+-comm {l = l} (suc n) m 
  ...| r rewrite sym r | +-comm n (suc m) | +-comm n m = refl

  drop-++-id : {A : Set}{l j : List A}
             → drop (length l) (l ++ j) ≡ j
  drop-++-id {l = []} = refl
  drop-++-id {l = x ∷ l} {j} = drop-++-id {l = l} {j = j}

  length-concat : {A : Set}(l : List (List A))
                → length (concat l) ≡ sum (map length l)
  length-concat []       = refl
  length-concat (a ∷ as)
    = trans (length-++ a)
            (cong (length a +_) (length-concat as))
  
  concat-map-map
    : {A B C : Set}{f : B → C}{g : A → List B}(l : List A)
    → concat (map (map f ∘ g) l)
    ≡ map f (concat (map g l))
  concat-map-map {f = f} {g = g} [] = refl
  concat-map-map {f = f} {g = g} (x ∷ l)
    rewrite concat-map-map {f = f} {g} l
      = sym (map-++-commute f (g x) (concat (map g l)))

  map-inj-inj : {A B : Set}(f : A → B)(f-inj : ∀ x y → f x ≡ f y → x ≡ y)
              → {l1 l2 : List A}
              → map f l1 ≡ map f l2
              → l1 ≡ l2
  map-inj-inj f f-inj {[]} {[]} hip = refl
  map-inj-inj f f-inj {[]} {x ∷ l2} ()
  map-inj-inj f f-inj {x ∷ l1} {[]} ()
  map-inj-inj f f-inj {x ∷ l1} {x₁ ∷ l2} hip
    = cong₂ _∷_ (f-inj x x₁ (p1 (∷-inj hip)))
                (map-inj-inj f f-inj {l1} {l2} (p2 (∷-inj hip)))

  non-empty : {A : Set}(l : List A)
            → ∃ (λ n → suc n ≡ length l)
            → A × List A
  non-empty [] (_ , ())
  non-empty (x ∷ l) hip = x , l

  open import Data.List.Any hiding (map)

  all-++ : {A : Set}{l2 : List A}
         → {P : A → Set}
         → (l1 : List A)
         → All P l1 → All P l2
         → All P (l1 ++ l2)
  all-++ [] hl1 hl2 = hl2
  all-++ (x ∷ xs) (px ∷ hl1) hl2
    = px ∷ all-++ xs hl1 hl2

  all-map : {A B : Set}{f : A → B}
          → {P : B → Set}(l : List A)
          → All (P ∘ f) l
          → All P (map f l)
  all-map [] hip = []
  all-map (x ∷ xs) (px ∷ hip)
    = px ∷ (all-map xs hip)

  all-pi : {A : Set}{P : A → Set}
         → ((a : A) → P a)
         → (l : List A)
         → All P l
  all-pi prf [] = []
  all-pi prf (x ∷ l) = (prf x) ∷ (all-pi prf l)

  all-⇒ : {A : Set}{P Q : A → Set}
        → (l : List A)
        → All P l
        → (∀ a → P a → Q a)
        → All Q l
  all-⇒ [] hip prf = []
  all-⇒ (x ∷ xs) (px ∷ hip) prf
    = (prf x px) ∷ (all-⇒ xs hip prf)

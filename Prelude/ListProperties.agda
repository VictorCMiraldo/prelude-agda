open import Prelude
open import Prelude.NatProperties using (suc-inj; +-comm)
open import Data.List using (drop)

module Prelude.ListProperties where

  open import Data.List.Properties
    using ( length-++; map-compose; map-++-commute
          ; length-map
          )
    public

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

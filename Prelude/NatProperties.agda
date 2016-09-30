open import Prelude

module Prelude.NatProperties where

  open import Data.Nat.Properties
    using ( ≤-steps; m≤m+n; n≤m+n; n≤1+n; 1+n≰n
          ; n≤m+n∸m; n∸n≡0; ∸-+-assoc; +-∸-assoc
          ; m+n∸n≡m; m+n∸m≡n; i+j≡0⇒i≡0; i+j≡0⇒j≡0
          ; cancel-+-left-≤; cancel-+-left
          )
    public
  open import Data.Nat.Properties.Simple
    using (+-comm; +-suc; +-assoc)
    public

  suc-inj : ∀{m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  +-inj-1 : ∀{m n o} → m + n ≡ m + o → n ≡ o
  +-inj-1 {zero} p = p
  +-inj-1 {suc m} p = +-inj-1 {m = m} (suc-inj p)

  +-inj-2 : ∀{m n o} → n + m ≡ o + m → n ≡ o
  +-inj-2 {m} {n} {o} p 
    rewrite +-comm n m 
          | +-comm o m
          = +-inj-1 {m = m} p

  +-exch : ∀ m n o p 
         → (m + n) + (o + p) ≡ (m + o) + (n + p)
  +-exch m n o p 
    = trans (+-assoc m n (o + p)) 
     (trans (cong (m +_) (sym (+-assoc n o p))) 
     (trans (cong (λ Q → m + (Q + p)) (+-comm n o))
     (trans (cong (m +_) (+-assoc o n p)) 
            (sym (+-assoc m o (n + p))))))

  ≤-refl : {m : ℕ} → m ≤ m
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  ≤-step : {n m : ℕ} → n ≤ m → n ≤ suc m
  ≤-step hip = ≤-steps 1 hip

  ≤-unstep : {n m : ℕ} → suc n ≤ m → n ≤ m
  ≤-unstep (s≤s p) = ≤-step p

  ≤-elim : {n m : ℕ} → m ≤ suc n → (m ≡ suc n → ⊥) → m ≤ n
  ≤-elim {_} {zero} prf n≢m         = z≤n
  ≤-elim {zero} {suc .0} (s≤s z≤n) n≢m = ⊥-elim (n≢m refl)
  ≤-elim {suc n} {suc m} (s≤s prf) n≢m 
    = s≤s (≤-elim prf (n≢m ∘ cong suc))

  ≤-elim' : {n m : ℕ} → n ≤ m → (¬ (n ≡ m)) → suc n ≤ m
  ≤-elim' {m = zero} z≤n hip = ⊥-elim (hip refl)
  ≤-elim' {m = suc m} z≤n hip = s≤s z≤n
  ≤-elim' (s≤s nm) hip = s≤s (≤-elim' nm (hip ∘ cong suc))

  ≤-abs : {n m : ℕ} → suc m ≤ n → m ≡ n → ⊥
  ≤-abs {m = zero} (s≤s p) ()
  ≤-abs {m = suc m} (s≤s p) q = ≤-abs p (suc-inj q)
  
  ≤-abs-0 : {m : ℕ} → suc m ≤ 0 → ⊥
  ≤-abs-0 ()

  ≤-strict : {n m : ℕ}{p : ¬ (n ≡ m)} 
           → suc n ≤ m → (n ≟-ℕ m) ≡ no p
  ≤-strict {n} {suc m} {p} (s≤s hip) 
    with n ≟-ℕ (suc m)
  ...| yes q = ⊥-elim (p q)
  ...| no ¬q = cong no (¬≡-pi ¬q p)

  +-≤-factor : {m n o : ℕ} → m + n ≡ o → m ≤ o 
  +-≤-factor {zero} prf = z≤n
  +-≤-factor {suc m} refl = s≤s (+-≤-factor refl)

  +-≤-split 
    : {m n o : ℕ} → m + n ≤ o → m ≤ o × n ≤ o
  +-≤-split {zero} prf = z≤n , prf
  +-≤-split {suc m} {o = zero} ()
  +-≤-split {suc m} {o = suc o} (s≤s prf)
    with +-≤-split {m} {o = o} prf
  ...| p1 , p2 = s≤s p1 , s≤ p2
    where
      s≤ : {n m : ℕ} → n ≤ m → n ≤ suc m
      s≤ z≤n     = z≤n
      s≤ (s≤s p) = s≤s (s≤ p)

  ≤-+-distr : {m n o p : ℕ} 
      → m ≤ o → n ≤ p → m + n ≤ o + p
  ≤-+-distr {o = zero} z≤n s = s
  ≤-+-distr {o = suc o} z≤n s = ≤-step (≤-+-distr {o = o} z≤n s)
  ≤-+-distr (s≤s r) s = s≤s (≤-+-distr r s)

  ≤-pi : {n m : ℕ} → (p q : n ≤ m) → p ≡ q
  ≤-pi z≤n z≤n = refl
  ≤-pi (s≤s p) (s≤s q) = cong s≤s (≤-pi p q)

  ≤-total : {m n : ℕ} → (m ≤ n → ⊥) → n ≤ m
  ≤-total {zero} hip = ⊥-elim (hip z≤n)
  ≤-total {suc m} {zero} hip = z≤n
  ≤-total {suc m} {suc n} hip = s≤s (≤-total (hip ∘ s≤s))

  ≤-trans : {m n o : ℕ} → m ≤ n → n ≤ o → m ≤ o
  ≤-trans z≤n s = z≤n
  ≤-trans (s≤s r) (s≤s s) = s≤s (≤-trans r s)

  ≤-yes : {m n : ℕ}(prf : m ≤ n) → (m ≤?-ℕ n) ≡ yes prf
  ≤-yes {m} {n} prf with m ≤?-ℕ n
  ...| no  abs = ⊥-elim (abs prf)
  ...| yes q   = cong yes (≤-pi q prf)

  1-≤-+-distr : (m n : ℕ) → 1 ≤ m + n → (1 ≤ m) ⊎ (1 ≤ n)
  1-≤-+-distr zero n hip    = i2 hip
  1-≤-+-distr (suc m) n hip = i1 (s≤s z≤n)

  m≢n-elim : (m n : ℕ) → (m ≡ n → ⊥) → ∃ (λ k → (m ≡ suc k) ⊎ (n ≡ suc k))
  m≢n-elim zero zero hip = ⊥-elim (hip refl)
  m≢n-elim zero (suc n) hip = n , i2 refl
  m≢n-elim (suc m) zero hip = m , i1 refl
  m≢n-elim (suc m) (suc n) hip = m , i1 refl

  m≢0-elim : (m : ℕ) → (m ≡ 0 → ⊥) → ∃ (λ k → m ≡ suc k)
  m≢0-elim zero hip = ⊥-elim (hip refl)
  m≢0-elim (suc m) hip = m , refl

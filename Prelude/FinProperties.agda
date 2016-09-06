open import Prelude

module Prelude.FinProperties where

  fs-inj : {n : ℕ}{i j : Fin n} → fs i ≡ fs j → i ≡ j
  fs-inj refl = refl

  Fink→A≈ListA : ∀{a}{A : Set a}{n : ℕ}
               → (Fin n → A) → List A
  Fink→A≈ListA {n = zero} f = []
  Fink→A≈ListA {n = suc n} f = f fz ∷ Fink→A≈ListA (f ∘ fs)

  Fink→A≈ListA-length
    : ∀{a}{A : Set a}{n : ℕ}
    → (f : Fin n → A)
    → length (Fink→A≈ListA f) ≡ n
  Fink→A≈ListA-length {n = zero} f = refl
  Fink→A≈ListA-length {n = suc n} f = cong suc (Fink→A≈ListA-length (f ∘ fs))

  Fin-split : {n m : ℕ} → Fin (n + m)
            → Fin n ⊎ Fin m
  Fin-split {0}     f       = i2 f
  Fin-split {suc n} fz      = i1 fz
  Fin-split {suc n} (fs f)  = [ i1 ∘ fs , i2 ]′ (Fin-split f) 

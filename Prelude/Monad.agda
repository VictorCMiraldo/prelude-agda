open import Prelude
open import Level using (Level; _⊔_; Lift)

module Prelude.Monad where

  ---------------------
  -- Monad Typeclass --
  ---------------------

  record Monad {a}(M : Set a → Set a) : Set (ls a) where
    infixl 1 _>>=_
    field
      return : {A : Set a} → A → M A
      _>>=_  : {A B : Set a} → M A → (A → M B) → M B

  open Monad {{...}}

  join : ∀{a}{M : Set a → Set a}{{m : Monad M}}{A : Set a}
       → M (M A) → M A
  join mma = mma >>= id

  mapM : ∀{a}{M : Set a → Set a}{{ m : Monad M}}{A B : Set a} 
       → (A → M B) → List A → M (List B)
  mapM f []       = return []
  mapM f (x ∷ la) = f x >>= (λ x' → mapM f la >>= return ∘ _∷_ x')

  mapM-map-compose : ∀{a}{M : Set a → Set a}{{ m : Monad M}}{A B C : Set a} 
                   → (fm : B → M C)(f : A → B)(l : List A)
                   → mapM fm (map f l) ≡ mapM (fm ∘ f) l
  mapM-map-compose fm f [] = refl
  mapM-map-compose fm f (x ∷ l)
    = cong (λ P → (fm (f x)) >>= P)
      (fun-ext (λ k → cong (λ P → _>>=_ P (return ∘ _∷_ k)) (mapM-map-compose fm f l)))

  zipWithM : ∀{a}{M : Set a → Set a}{{ m : Monad M}}{A B C : Set a} 
           → (A → B → M C) → List A → List B → M (List C)
  zipWithM f [] [] = return []
  zipWithM f [] (x ∷ lb) = return []
  zipWithM f (x ∷ la) [] = return []
  zipWithM f (a ∷ la) (b ∷ lb)
    = f a b >>= λ c → zipWithM f la lb >>= λ cs → return (c ∷ cs)

  _>>_ : ∀{a}{M : Set a → Set a}{{ m : Monad M }}{A B : Set a}
       → M A → M B → M B
  f >> g = f >>= λ _ → g

  -- Binds the side-effects of the second computation,
  -- returning the value of the first.
  _<>=_ : ∀{a}{M : Set a → Set a}{{ m : Monad M }}{A B : Set a}
        → M A → (A → M B) → M A
  f <>= x = f >>= λ r → x r >> return r

  {-
  _<$>_ : ∀{a}{A B : Set a}{M : Set a → Set a}{{ m : Monad M }}
        → (A → B) → M A → M B
  f <$> x = ?
  -}

  -------------------------------------
  -- Laws for reasoning over Monads  --
  -------------------------------------

  record Lawfull (M : Set → Set){{m : Monad M}} : Set1  where
    field
      left-id  : {A B : Set}{x : A}{f : A → M B}
               → (return x >>= f) ≡ f x
      right-id : {A B : Set}{m : M A}
               → (m >>= return) ≡ m
      assoc    : {A B C : Set}{m : M A}{f : A → M B}{g : B → M C}
               → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))


  -----------------
  -- Maybe Monad --
  -----------------

  _<$>+1_ : ∀{a}{A B : Set a} → (A → B) → Maybe A → Maybe B
  f <$>+1 x with x
  ...| nothing = nothing
  ...| just x' = just (f x')

  instance
    MonadMaybe : ∀{a} → Monad {a} Maybe
    MonadMaybe = record
      { return = just
      ; _>>=_  = λ { nothing  _ → nothing 
                   ; (just x) f → f x 
                   }
      }

  -----------------
  -- State Monad --
  -----------------

  record ST (s a : Set) : Set where
    field run : s → (a × s)

  evalST : ∀{a s} → ST s a → s → a
  evalST s = p1 ∘ (ST.run s)

  get : ∀{s} → ST s s
  get = record { run = λ s → (s , s) }

  put : ∀{s} → s → ST s Unit
  put s = record { run = λ _ → (unit , s) }

  instance
    MonadState : ∀{s} → Monad (ST s)
    MonadState = record
      { return = λ a → record { run = λ s → a , s }
      ; _>>=_  = λ x f → record { run = 
                 λ s → let y = ST.run x s
                       in ST.run (f (p1 y)) (p2 y)
                }
      }

  ST-join-p2 : {S A B : Set}{f : ST S A}{g : ST S B}(s₀ : S) 
             → p2 (ST.run f (p2 (ST.run g s₀))) ≡ p2 (ST.run (g >> f) s₀)
  ST-join-p2 {g = g} s
    with ST.run g s
  ...| r = refl

  ---------------------
  -- Decorated State --
  ---------------------
  
  {-
  -- Hoare states, as defined by Swierstra.
  module HoareState (S : Set) where
    Pre : Set1
    Pre = S → Set

    Post : Set → Set1
    Post A = S → A → S → Set

    HS : Pre → (A : Set) → Post A → Set
    HS pre A post 
      = (i : Σ S pre) → Σ (A × S) (λ as → post (p1 i) (p1 as) (p2 as))

    returnHS : {A : Set}(a : A) → HS (λ _ → Unit) A (λ i y f → i ≡ f × y ≡ a)
    returnHS a (s , ps) = (a , s) , refl , refl

    bindHS : {A B : Set}{P₁ : Pre}{Q₁ : Post A}{P₂ : A → Pre}{Q₂ : A → Post B}
           → HS P₁ A Q₁ → ((x : A) → HS (P₂ x) B (Q₂ x)) 
           → HS (λ s₁ → P₁ s₁ × ((x : A)(s₂ : S) → Q₁ s₁ x s₂ → P₂ x s₂))
                B
                (λ s₁ y s₃ → Σ A (λ x → Σ S (λ s₂ → Q₁ s₁ x s₂ × Q₂ x s₂ y s₃)))
    bindHS hsA hsAB (s , ps) with hsA (s , p1 ps)
    ...| ((a , s₁) , r) with hsAB a (s₁ , p2 ps a s₁ r)
    ...| ((b , s₂) , r') = (b , s₂) , (a , (s₁ , (r , r')))

    getHS : HS (λ _ → Unit) S (λ s₀ r s₁ → s₀ ≡ r × r ≡ s₁)
    getHS (s , ps) = (s , s) , (refl , refl)

    putHS : (s : S) → HS (λ _ → Unit) Unit (λ s₀ r s₁ → s₁ ≡ s)
    putHS s _ = (unit , s) , refl

  record HST (s a : Set) : Set where
    open HoareState s
    field
      run : {P : Pre}{Q : Post a} → HS P a Q 

  record Monad1 {a}(M : Set a → Set (ls a)) : Set (ls (ls a)) where
    infixl 1 _>>=1_
    field
      return1 : {A : Set a} → A → M A
      _>>=1_  : {A B : Set a} → M A → (A → M B) → M B

  instance
    monad-hst : ∀{s} → Monad1 (HST s)
    monad-hst {s} = record 
      { return1 = λ x → record { run = {!returnHS x!} } 
      ; _>>=1_ = {!!} 
      }
      where 
        open HoareState s
  -}

  ------------------
  -- StateT Maybe --
  ------------------

  record STM (s a : Set) : Set where
    field run : s → Maybe (a × s)

  evalSTM : ∀{a s} → STM s a → s → Maybe a
  evalSTM f s = p1 <$>+1 (STM.run f s)

  getm : ∀{s} → STM s s
  getm = record { run = λ s → just (s , s) }

  putm : ∀{s} → s → STM s Unit
  putm s = record { run = λ _ → just (unit , s) }

  failSTM : ∀{s a} → STM s a
  failSTM = record { run = λ _ → nothing }

  private
    bindSTM : ∀{s a b} → STM s a → (a → STM s b) → STM s b
    bindSTM sa f = record { run = λ s → (STM.run sa s) >>= (λ s' → STM.run (f (p1 s')) (p2 s')) }

  instance
    MonadStateM : ∀{s} → Monad (STM s)
    MonadStateM = record
      { return = λ a → record { run = λ s → just (a , s) }
      ; _>>=_  = bindSTM
      }

  -- Universe Polymorphic version of the state monad.
  record STₐ {a b}(s : Set a)(o : Set b) : Set (a ⊔ b) where
    field run : s → (o × s)

  evalSTₐ : ∀{a b}{s : Set a}{o : Set b} → STₐ s o → s → o
  evalSTₐ s = p1 ∘ (STₐ.run s)

  getₐ : ∀{a}{s : Set a} → STₐ s s
  getₐ = record { run = λ s → (s , s) }

  putₐ : ∀{a}{s : Set a} → s → STₐ s Unit
  putₐ s = record { run = λ _ → (unit , s) }

  instance
    MonadStateₐ : ∀{a b}{s : Set a} → Monad {a ⊔ b} (STₐ s)
    MonadStateₐ = record
      { return = λ x → record { run = λ s → x , s }
      ; _>>=_  = λ x f → record { run = 
                 λ s → let y = STₐ.run x s
                       in STₐ.run (f (p1 y)) (p2 y)
                }
      }

  -------------
  -- Fresh ℕ --
  -------------

  Freshℕ : Set → Set
  Freshℕ A = ST ℕ A

  runFresh : ∀{A} → Freshℕ A → A
  runFresh f = evalST f 0

  runFresh-n : ∀{A} → Freshℕ A → ℕ → A
  runFresh-n = evalST

  inc : Freshℕ Unit
  inc = get >>= (put ∘ suc)

  ----------------
  -- List Monad --
  ----------------

  NonDet : ∀{a} → Set a → Set a
  NonDet A = List A

  NonDetBind : ∀{a}{A B : Set a} → NonDet A → (A → NonDet B) → NonDet B
  NonDetBind x f = concat (map f x)

  NonDetRet : ∀{a}{A : Set a} → A → NonDet A
  NonDetRet x = x ∷ []

  NonDetApp : ∀{a}{A B : Set a} → NonDet (A → B) → NonDet A → NonDet B
  NonDetApp [] xs       = []
  NonDetApp (x ∷ gs) xs = map x xs ++ NonDetApp gs xs

  instance
    MonadNonDet : ∀{a} → Monad {a} NonDet
    MonadNonDet = record
      { return = NonDetRet
      ; _>>=_  = NonDetBind
      }

  ------------------
  -- Reader Monad --
  ------------------

  Reader : ∀{a b} → Set a → Set b → Set (a ⊔ b)
  Reader R A = R → A

  reader-bind : ∀{a b}{R : Set a}{A B : Set b}
              → Reader R A → (A → Reader R B) → Reader R B
  reader-bind ra rb = λ r → rb (ra r) r

  reader-return : ∀{a b}{R : Set a}{A : Set b}
                → A → Reader R A
  reader-return a = λ _ → a

  reader-local : ∀{a b}{R : Set a}{A : Set b}
               → (R → R) → Reader R A → Reader R A
  reader-local f ra = ra ∘ f

  reader-ask : ∀{a}{R : Set a} → Reader R R
  reader-ask = id

  instance
    MonadReader : ∀{a b}{R : Set a} → Monad {b ⊔ a} (Reader {b = b ⊔ a} R)
    MonadReader = record
      { return = reader-return
      ; _>>=_  = reader-bind
      }

  module Applicative where
    
    record IsApplicative {a}{M : Set a → Set a}
            (m : Monad M) : Set (ls a) where
      constructor app
      infixl 20 _<*>_
      field
        _<*>_ : {A B : Set a} → M (A → B) → M A → M B      

    open IsApplicative {{...}}

    infixl 20 _<$>_
    _<$>_ : ∀{a}{M : Set a → Set a}{{m : Monad M}}
             {{app : IsApplicative m}}{A B : Set a}
          → (A → B) → M A → M B
    _<$>_ {{_}} {{app go}} f a = go (return f) a
    

    instance
      maybe-app : ∀{a} → IsApplicative {a} MonadMaybe
      maybe-app = record { _<*>_ = _<M*>_ }

      list-app : ∀{a} → IsApplicative {a} MonadNonDet
      list-app = app NonDetApp

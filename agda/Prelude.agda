{-# OPTIONS --rewriting #-}

module Prelude where

  open import Agda.Primitive public using (lzero)
    renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

  -- Rewriting
  infix 30 _↦_
  postulate  
    _↦_ : ∀ {i} {A : Set i} → A → A → Set i

  {-# BUILTIN REWRITE _↦_ #-}

  record ⊤ {i} : Set i where
    constructor tt

  data ⊥ : Set where
  
  infixr 60 _,_

  record Σ {i j} (A : Set i) (B : A → Set j) : Set (lmax i j) where
    constructor _,_
    field 
     fst : A
     snd : B fst

  open Σ public

  _×_ : ∀ {i j} → Set i → Set j → Set (lmax i j)
  A × B = Σ A (λ _ → B)
  
  data Bool : Set where
    true : Bool
    false : Bool

  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ 

  {-# BUILTIN NATURAL ℕ #-}

  data _⊔_ (A B : Set) : Set where
    inl : A → A ⊔ B
    inr : B → A ⊔ B

  infixl 30 _==_
  
  data _==_ {i} {A : Set i} (x : A) : A → Set i where
    idp : x == x

  {- Inequalities -}
  infix 40 _<_ _≤_ _≥_

  data _<_ : ℕ → ℕ → Set where
    ltS : {m : ℕ} → m < (S m)
    ltSR : {m n : ℕ} → m < n → m < (S n)

  OltS : {m : ℕ} → O < S m
  OltS {O} = ltS
  OltS {S m} = ltSR OltS 

  <-inj : {m n : ℕ} → S m < S n → m < n
  <-inj {m} {O} (ltSR ())
  <-inj {.n} {S n} ltS = ltS
  <-inj {m} {S n} (ltSR e) = ltSR (<-inj {m} {n} e)
  
  _≤_ : ℕ → ℕ → Set
  m ≤ n = (m == n) ⊔ (m < n) 

  _≥_ : ℕ → ℕ → Set
  m ≥ n = m < n → ⊥

  max : ℕ → ℕ → ℕ
  max O m = m
  max (S n) O = S n
  max (S n) (S m) = S (max n m)

  data List (A : Set) : Set where
    nil : List A
    cns : A → List A → List A

  map : {A B : Set} → (A → B) → List A → List B
  map f nil = nil
  map f (cns a as) = cns (f a) (map f as)
  
  foldr : {A B : Set} → List A
    → (f : A → B → B)
    → B → B
  foldr nil f b = b
  foldr (cns a l) f b = f a (foldr l f b)

  record Stream (A : Set) : Set where
    coinductive
    field
      hd : A
      tl : Stream A ⊔ ⊤ 

  --
  --  Equality Lemmas
  --
  
  ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
    → {a₀ a₁ : A} (p : a₀ == a₁)
    → f a₀ == f a₁
  ap f idp = idp

  ! : ∀ {i} {A : Set i} {a₀ a₁ : A}
    → a₀ == a₁ → a₁ == a₀
  ! idp = idp

  infixr 10 _∙_

  _∙_ : ∀ {i} {A : Set i} {a₀ a₁ a₂ : A}
    → a₀ == a₁ → a₁ == a₂
    → a₀ == a₂
  idp ∙ idp = idp
  
  -- Equational reasoning ...
  infixr 10 _=⟨_⟩_
  infix  15 _=∎

  _=⟨_⟩_ : ∀ {i} {A : Set i} (x : A) {y z : A} → x == y → y == z → x == z
  _ =⟨ idp ⟩ idp = idp

  _=∎ : ∀ {i} {A : Set i} (x : A) → x == x
  _ =∎ = idp

  infixl 40 ap
  syntax ap f p = p |in-ctx f

  transport : ∀ {i j} {A : Set i} (P : A → Set j)
    → {a₀ a₁ : A} (q : a₀ == a₁)
    → P a₀ → P a₁
  transport P idp p = p

  ×-cong : ∀ {i j} {A : Set i} {B : Set j}
    → {a₀ a₁ : A} {b₀ b₁ : B}
    → (p : a₀ == a₁) (q : b₀ == b₁)
    → (a₀ , b₀) == (a₁ , b₁)
  ×-cong idp idp = idp

  Σ-cong : ∀ {i j} {A : Set i} {B : A → Set j}
    → {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁}
    → (p : a₀ == a₁) (q : transport B p b₀ == b₁)
    → (a₀ , b₀) == (a₁ , b₁)
  Σ-cong idp idp = idp

  transport-× : ∀ {i j} {A : Set i} {B : A → Set j}
    → {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B a₀}
    → transport (λ a → B a × B a) p (b₀ , b₁)
      == (transport B p b₀ , transport B p b₁)
  transport-× idp = idp

  uip : ∀ {i} {A : Set i} {a₀ a₁ : A}
    → (p : a₀ == a₁) (q : a₀ == a₁)
    → p == q
  uip idp idp = idp

  triple-trans-lemma : ∀ {i j} {A : Set i} {B : A → Set j}
    → {a₀ a₁ a₂ a₃ : A} {b₀ : B a₀} {b₃ : B a₃}
    → (p : a₁ == a₂) (q : a₀ == a₁) (r : a₃ == a₂)
    → transport B (q ∙ p ∙ (! r)) b₀ == b₃
    → transport B p (transport B q b₀) == transport B r b₃
  triple-trans-lemma idp idp idp p = p

  -- trans-invar : ∀ {i j} {A : Set i} {B : A → Set j}
  --   → {a₀ a₁ : A} {b₀ : B a₀}
  --   → (p : a₀ == a₁) (q : a₀ == a₁)
  --   → transport B p b₀ == transport B q b₀
  -- trans-inver = {!!}

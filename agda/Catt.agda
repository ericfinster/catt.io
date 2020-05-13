--
--  A formalization of the language of Catt
--

open import Prelude

module Catt where

  data Ctx : Set 
  data Sub : Set
  data Type : Set
  data Term : Set

  data _⊢ : Ctx → Set
  data _⊢_ : Ctx → Type → Set
  data _⊢_∷_ : Ctx → Term → Type → Set
  data _∷_⇒_ : Sub → Ctx → Ctx → Set 

  _⊢ps : Ctx → Set
  data ⊢ps₀ : Ctx → Type → ℕ → Set

  data _⊢_∎ : Ctx → Type → Set

  _[_]ty : Type → Sub → Type
  _[_]tm : Term → Sub → Term

  _∘_ : Sub → Sub → Sub 

  infixl 80 _∣_ _∥_
  
  data Ctx where
    ● : Ctx
    _∣_ : (Γ : Ctx) (A : Type) → Ctx

  data Sub where
    ● : Sub
    _∥_ : Sub → Term → Sub

  data Type where
    ⋆ : Type
    hom : (A : Type) (a : Term) (b : Term) → Type

  data Term where
    var : (n : ℕ) → Term
    coh : (Γ : Ctx) (A : Type) (σ : Sub) → Term

  --
  --  Dimensions
  --
  
  dim-ty : Type → ℕ
  dim-ty ⋆ = O
  dim-ty (hom A a b) = S (dim-ty A)
  
  dim-ctx : Ctx → ℕ
  dim-ctx ● = O -- Hmmm.  Shouldn't this be -1?
  dim-ctx (Γ ∣ A) = max (dim-ctx Γ) (dim-ty A)

  data _has-dim_in-ctx_ : ℕ → ℕ → Ctx → Set where
    O-has-dim-ty : {Γ : Ctx} {A : Type}
      → O has-dim (dim-ty A) in-ctx Γ ∣ A
    S-has-dim-prev : {Γ : Ctx} {A : Type} {i d : ℕ}
      → i has-dim d in-ctx Γ
      → S i has-dim d in-ctx Γ ∣ A
      
  --
  -- de Bruijn lifting
  --

  infixl 90 _↑ty _↑tm _↑sub
  
  _↑ty : Type → Type
  _↑tm : Term → Term
  _↑sub : Sub → Sub

  ⋆ ↑ty = ⋆
  hom A a b ↑ty = hom (A ↑ty) (a ↑tm) (b ↑tm)

  var n ↑tm = var (S n)
  coh Γ A σ ↑tm = coh Γ A (σ ↑sub)

  ● ↑sub = ●
  (σ ∥ a) ↑sub = σ ↑sub ∥ a ↑tm

  --
  --  Substitution Implementation
  --

  ⋆ [ σ ]ty = ⋆
  hom A a b [ σ ]ty =
    hom (A [ σ ]ty) (a [ σ ]tm) (a [ σ ]tm)

  -- The base case here is in fact an error.  However,
  -- this should never occur for well-typed terms.  Hence
  -- we return a dummy value so that the function remains
  -- total.
  var n [ ● ]tm = var n
  var O [ σ ∥ a ]tm = a
  var (S n) [ σ ∥ a ]tm = var n [ σ ]tm
  coh Γ A τ [ σ ]tm = coh Γ A (τ ∘ σ)

  ● ∘ σ = ●
  (τ ∥ a) ∘ σ = τ ∘ σ ∥ (a [ σ ]tm)

  --
  --  Occurrence relations
  --

  infixl 30 _∈ctx_
  
  data _∈ctx_ : ℕ → Ctx → Set
  data _∈tm_ : ℕ → Term → Set
  data _∈ty_ : ℕ → Type → Set
  data _∈sub_ : ℕ → Sub → Set 

  data _∈ctx_ where
    O∈ctx : (Γ : Ctx) (A : Type) → O ∈ctx Γ ∣ A
    S∈ctx : (Γ : Ctx) (A : Type) (n : ℕ)
      → n ∈ctx Γ
      → (S n) ∈ctx Γ ∣ A

  data _∈tm_ where
    var∈tm : (n : ℕ) → n ∈tm var n
    coh∈tm : {n : ℕ} (Γ : Ctx) (A : Type) (σ : Sub)
      → n ∈sub σ → n ∈tm coh Γ A σ

  data _∈ty_ where
    ty∈ty : (A : Type) (a : Term) (b : Term)
      → (n : ℕ) (n∈tyA : n ∈ty A)
      → n ∈ty hom A a b
    src∈ty : (A : Type) (a : Term) (b : Term)
      → (n : ℕ) (n∈tma : n ∈tm a)
      → n ∈ty hom A a b
    tgt∈ty : (A : Type) (a : Term) (b : Term)
      → (n : ℕ) (n∈tmb : n ∈tm b)
      → n ∈ty hom A a b

  data _∈sub_ where
    tm∈sub : {n : ℕ} (σ : Sub) (t : Term)
      → n ∈tm t
      → n ∈sub (σ ∥ t)
    wk∈sub : {n : ℕ} (σ : Sub) (t : Term)
      → n ∈sub σ
      → n ∈sub (σ ∥ t)

  --
  --  Pasting diagrams and fullness
  --

  data ⊢ps₀ where
    ps● : ⊢ps₀ (● ∣ ⋆) ⋆ O
    ps↑ : {Γ : Ctx} {A : Type} {k : ℕ}
      → ⊢ps₀ Γ A k
      → ⊢ps₀ (Γ ∣ A ↑ty ∣ hom (A ↑ty ↑ty) (var (S k)) (var O))
             (hom (A ↑ty ↑ty) (var (S k)) (var O)) O
    ps↓ : {Γ : Ctx} {A : Type} {s t : ℕ} {k : ℕ}
      → ⊢ps₀ Γ (hom A (var s) (var t)) k
      → ⊢ps₀ Γ A (S t)

  -- The number n will be the de Bruijn index of
  -- the last object in the pasting diagram.
  Γ ⊢ps = Σ ℕ (λ k → ⊢ps₀ Γ ⋆ k)

  infixl 30 _∈src_ _∈tgt_

  -- Verify that these predicates are working as expected!!!
  data _∈src_ : {Γ : Ctx} {A : Type} {k : ℕ} → ℕ → ⊢ps₀ Γ A k → Set where
  
    -- Sources are tagged when descending
    src∈ps↓ : {Γ : Ctx} {A : Type} {s t : ℕ} {k : ℕ}
      → (Γ⊢ps₀ : ⊢ps₀ Γ (hom A (var s) (var t)) k)
      → (S s) ∈src ps↓ Γ⊢ps₀
      
    -- Previously tagged variables extend
    src∈ps↑ : {Γ : Ctx} {A : Type} {k : ℕ}
      → (Γ⊢ps₀ :  ⊢ps₀ Γ A k)
      → (i : ℕ) (n∈src-ps : i ∈src Γ⊢ps₀)
      → (S (S i)) ∈src (ps↑ Γ⊢ps₀)

  data _∈tgt_ : {Γ : Ctx} {A : Type} {k : ℕ} → ℕ → ⊢ps₀ Γ A k → Set where
  
    -- Targets are tagged when descending
    tgt∈ps↓ : {Γ : Ctx} {A : Type} {s t : ℕ} {k : ℕ}
      → (Γ⊢ps₀ : ⊢ps₀ Γ (hom A (var s) (var t)) k)
      → (S t) ∈tgt ps↓ Γ⊢ps₀
      
    -- Previously tagged variables extend
    tgt∈ps↑ : {Γ : Ctx} {A : Type} {k : ℕ}
      → (Γ⊢ps₀ :  ⊢ps₀ Γ A k)
      → (i : ℕ) (n∈tgt-ps : i ∈tgt Γ⊢ps₀)
      → (S (S i)) ∈tgt (ps↑ Γ⊢ps₀)

  is-src-var : (Γ : Ctx) (Γ⊢ps : Γ ⊢ps) → ℕ → Set
  is-src-var Γ Γ⊢ps i =
    Σ ℕ (λ d →
    Σ (i has-dim d in-ctx Γ) (λ _ →
    S d < dim-ctx Γ ⊔ (S d == dim-ctx Γ × (i ∈src (snd Γ⊢ps)))))

  is-tgt-var : (Γ : Ctx) (Γ⊢ps : Γ ⊢ps) → ℕ → Set
  is-tgt-var Γ Γ⊢ps i =
    Σ ℕ (λ d →
    Σ (i has-dim d in-ctx Γ) (λ _ →
    S d < dim-ctx Γ ⊔ (S d == dim-ctx Γ × (i ∈tgt (snd Γ⊢ps)))))

  data _⊢_∎ where
    coh-full : {Γ : Ctx} {Γ⊢ps : Γ ⊢ps}
      → (A : Type) (Γ⊢A : Γ ⊢ A)
      → (a : Term) (Γ⊢a∷A : Γ ⊢ a ∷ A)
      → (b : Term) (Γ⊢b∷A : Γ ⊢ b ∷ A)
      → (is-alg : (i : ℕ) (i∈ctxΓ : i ∈ctx Γ) → i ∈ty hom A a b)
      → Γ ⊢ hom A a b ∎
    comp-full : {Γ : Ctx} {Γ⊢ps : Γ ⊢ps}
      → (A : Type) (Γ⊢A : Γ ⊢ A)
      → (a : Term) (Γ⊢a∷A : Γ ⊢ a ∷ A)
      → (b : Term) (Γ⊢b∷A : Γ ⊢ b ∷ A)
      -- these should be propositional, and we should use equivalences
      → (a-src-to : (i : ℕ) → is-src-var Γ Γ⊢ps i → i ∈tm a)
      → (a-src-from : (i : ℕ) → i ∈tm a → is-src-var Γ Γ⊢ps i)
      → (b-tgt-to : (i : ℕ) → is-tgt-var Γ Γ⊢ps i → i ∈tm b)
      → (b-tgt-from : (i : ℕ) → i ∈tm b → is-tgt-var Γ Γ⊢ps i)
      → Γ ⊢ hom A a b ∎

  --
  --  Typing relations 
  --
  
  data _⊢ where
    ●⊢ : ● ⊢
    _,⊢_ : {Γ : Ctx} {A : Type} 
      → (Γ⊢ : Γ ⊢) (Γ⊢A : Γ ⊢ A)
      → Γ ∣ A ⊢

  data _⊢_ where
    Γ⊢⋆ : (Γ : Ctx) (Γ⊢ : Γ ⊢)
      → Γ ⊢ ⋆
    hom⊢ : (Γ : Ctx) (A : Type)
      → (a : Term) (b : Term)
      → (Γ⊢ : Γ ⊢) (Γ⊢A : Γ ⊢ A)
      → (Γ⊢a∷A : Γ ⊢ a ∷ A)
      → (Γ⊢b∷A : Γ ⊢ b ∷ A)
      → Γ ⊢ hom A a b

  data _⊢_∷_ where

    -- Variable typing
    var⊢ : (Γ : Ctx) (A : Type)
      → Γ ∣ A ⊢ var O ∷ A
    var↑ : (Γ : Ctx) (A B : Type)
      → (n : ℕ) (Γ⊢n : Γ ⊢ var n ∷ B)
      → Γ ∣ A ⊢ var (S n) ∷ B

    -- coherence typing
    coh⊢ : (Γ Δ : Ctx) (Γ⊢ps : Γ ⊢ps)
      → (A : Type) (Γ⊢A∎ : Γ ⊢ A ∎)
      → (σ : Sub) (σ∷Δ⇒Γ : σ ∷ Δ ⇒ Γ)
      → Δ ⊢ coh Γ A σ ∷ (A [ σ ]ty)

  data _∷_⇒_ where
    Γ! : (Γ : Ctx) (Γ⊢ : Γ ⊢)
      → ● ∷ Γ ⇒ ● 
    ext⇒ : (Γ Δ : Ctx) (A : Type)
      → (Γ⊢ : Γ ⊢) (Δ⊢ : Δ ⊢) (Δ⊢A : Δ ⊢ A)
      → (σ : Sub) (σ∷Γ⇒Δ : σ ∷ Γ ⇒ Δ)
      → (a : Term) (Γ⊢a∷A[σ] : Γ ⊢ a ∷ (A [ σ ]ty))
      → (σ ∥ a) ∷ Γ ⇒ Δ ∣ A

  --
  --  Auxillary definitions and examples
  --

  -- A predicate for locally maximal variables
  data locmax : {Γ : Ctx} {A : Type} {k : ℕ} (Γ⊢ps₀ : ⊢ps₀ Γ A k) → ℕ → Set where
    locmax● : locmax ps● O
    locmax↕ : {Γ : Ctx} {A : Type} {k : ℕ}
      → {Γ⊢ps₀ : ⊢ps₀ Γ A k}
      → locmax (ps↓ (ps↑ Γ⊢ps₀)) O
    locmax↑ : {Γ : Ctx} {A : Type} {k : ℕ}
      → {Γ⊢ps₀ : ⊢ps₀ Γ A k} {i : ℕ}
      → locmax Γ⊢ps₀ i 
      → locmax (ps↑ Γ⊢ps₀) (S (S i))
    locmax↓ : {Γ : Ctx} {A : Type} {s t : ℕ} {k : ℕ}
      → {Γ⊢ps₀ : ⊢ps₀ Γ (hom A (var s) (var t)) k}
      → {i : ℕ} (lm : locmax Γ⊢ps₀ i)
      → locmax (ps↓ Γ⊢ps₀) i

  -- Example Pasting Diagrams
  arrow : Ctx
  arrow = ● ∣ ⋆
            ∣ ⋆ ∣ hom ⋆ (var 1) (var 0)

  arrow-ps : ⊢ps₀ arrow ⋆ 1
  arrow-ps = ps↓ (ps↑ ps●)

  arrow-src : 2 ∈src arrow-ps
  arrow-src = src∈ps↓ (ps↑ ps●)

  comp₃ : Ctx
  comp₃ = ● ∣ ⋆
            ∣ ⋆ ∣ hom ⋆ (var 1) (var 0)
            ∣ ⋆ ∣ hom ⋆ (var 2) (var 0)
            ∣ ⋆ ∣ hom ⋆ (var 2) (var 0)

  comp₃-ps : ⊢ps₀ comp₃ ⋆ 1
  comp₃-ps = ps↓ (ps↑ (ps↓ (ps↑ (ps↓ (ps↑ ps●)))))
          
  horiz : Ctx
  horiz = ● ∣ ⋆
            ∣ ⋆ ∣ hom ⋆ (var 1) (var 0)
                ∣ hom ⋆ (var 2) (var 1) ∣ hom (hom ⋆ (var 3) (var 2)) (var 1) (var 0)
            ∣ ⋆ ∣ hom ⋆ (var 4) (var 0)
                ∣ hom ⋆ (var 5) (var 1) ∣ hom (hom ⋆ (var 6) (var 2)) (var 1) (var 0)

  horiz-ps : ⊢ps₀ horiz ⋆ 3
  horiz-ps = ps↓ (ps↓ (ps↑ (ps↑ (ps↓ (ps↓ (ps↑ (ps↑ ps●)))))))

  horiz-locmax₀ : locmax horiz-ps 0
  horiz-locmax₀ = locmax↓ locmax↕

  -- Cannot stop at index 2, as expected ...
  -- horiz-locmax₂ : locmax horiz-ps 2
  -- horiz-locmax₂ = locmax↓ (locmax↓ (locmax↑ {!!}))

  horiz-locmax₄ : locmax horiz-ps 4
  horiz-locmax₄ = locmax↓ (locmax↓ (locmax↑ (locmax↑ (locmax↓ locmax↕))))

  vert : Ctx
  vert = ● ∣ ⋆
           ∣ ⋆ ∣ hom ⋆ (var 1) (var 0)
               ∣ hom ⋆ (var 2) (var 1) ∣ hom (hom ⋆ (var 3) (var 2)) (var 1) (var 0)
               ∣ hom ⋆ (var 4) (var 3) ∣ hom (hom ⋆ (var 5) (var 4)) (var 2) (var 0)

  vert-ps : ⊢ps₀ vert ⋆ 5
  vert-ps = ps↓ (ps↓ (ps↑ (ps↓ (ps↑ (ps↑ ps●)))))

  vert-locmax₀ : locmax vert-ps 0
  vert-locmax₀ = locmax↓ locmax↕

  vert-locmax₂ : locmax vert-ps 2
  vert-locmax₂ = locmax↓ (locmax↓ (locmax↑ locmax↕))

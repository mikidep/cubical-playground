module CubicalPlayground.Prelude where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function using (_∘_; flip; ∘-assoc)

module PathReasoning where
  private
    variable
      ℓ : Level
      A : Type ℓ

  ≡⟨-⟩∎-syntax : ∀ (x y : A) → x ≡ y → x ≡ y
  ≡⟨-⟩∎-syntax _ _ p = p
  {-# INLINE ≡⟨-⟩∎-syntax #-}

  syntax ≡⟨-⟩∎-syntax x y p = x ≡⟨ p ⟩∎ y ∎

  infixr 3 ≡⟨-⟩∎-syntax

  ≡⟨⟩∎-syntax : ∀ {x : A} (y : A) → x ≡ y → x ≡ y
  ≡⟨⟩∎-syntax _ p = p
  {-# INLINE ≡⟨⟩∎-syntax #-}

  syntax ≡⟨⟩∎-syntax y p = p ≡⟨⟩∎ y
  infixl 1.75 ≡⟨⟩∎-syntax

open PathReasoning using (≡⟨-⟩∎-syntax; ≡⟨⟩∎-syntax) public

infixr 5 _$_
_$_ : {ℓ ℓ' : _} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
f $ x = f x

module _
  {ℓ ℓ' ℓ'' : Level}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {C : (a : A) → B a → Type ℓ''} where

  infixl 9 _»_
  _»_ : (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) → (a : A) → C a (f a)
  _»_ f g x = g (f x) 

module _
  {ℓ ℓ' ℓ'' ℓ''' : Level}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {C : (a : A) → B a → Type ℓ''}
  {D : (a : A) (b : B a) → C a b → Type ℓ'''} where

  »-assoc : (f : (a : A) → B a)
            (g : {a : A} → (b : B a) → C a b)
            (h : {a : A} {b : B a} → (c : C a b) → D a b c)
          → f » g » h ≡ f » (g » h)
  »-assoc f g h = ∘-assoc h g f

≡[-]-syntax :
  ∀ {ℓa ℓb}
  {A : Type ℓa}
  {x y : A}
  (p : x ≡ y)
  (B : A → Type ℓb)
  (xb : B x)
  (yb : B y)
  → Type ℓb
≡[-]-syntax p B xb yb = PathP (λ i → B (p i)) xb yb

syntax ≡[-]-syntax p B xb yb = xb ≡[ p , B ] yb
infix 4 ≡[-]-syntax

module PathOverReasoning
  {ℓa}
  {A : Type ℓa}
  where

  ≡[-]⟨-⟩-syntax :
    ∀ {ℓb}
    {x y z : A}
    (p : x ≡ y)
    (B : A → Type ℓb)
    (xb : B x)
    {yb : B y}
    {zb : B z}
    (po-p : xb ≡[ p , B ] yb)
    {q : y ≡ z}
    (po-q : yb ≡[ q , B ] zb)
    → xb ≡[ p ∙ q , B ] zb
  ≡[-]⟨-⟩-syntax _ B _ po-p po-q = compPathP' {B = B} po-p po-q

  ≡[-]⟨-⟩∎-syntax :
    ∀ {ℓb}
    {x y : A}
    (p : x ≡ y)
    (B : A → Type ℓb)
    (xb : B x)
    (yb : B y)
    (po-p : xb ≡[ p , B ] yb)
    → xb ≡[ p , B ] yb
  ≡[-]⟨-⟩∎-syntax _ _ _ _ po-p = po-p

  syntax ≡[-]⟨-⟩-syntax xb B po-p po-q = xb ≡[ p , B ]⟨ po-p ⟩ po-q
  infixr 2 ≡[-]⟨-⟩-syntax
  syntax ≡[-]⟨-⟩∎-syntax p B xb yb po-p = xb ≡[ p , B ]⟨ po-p ⟩∎ yb ∎
  infix 3 ≡[-]⟨-⟩∎-syntax

open PathOverReasoning public
module CubicalPlayground.Prelude where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function using (_∘_; flip; ∘-assoc)

module PathReasoning where
  private
    variable
      ℓ : Level
      A : Type ℓ

  ≡⟨⟩∎-syntax : ∀ (x y : A) → x ≡ y → x ≡ y
  ≡⟨⟩∎-syntax _ _ p = p
  {-# INLINE ≡⟨⟩∎-syntax #-}

  syntax ≡⟨⟩∎-syntax x y p = x ≡⟨ p ⟩∎ y ∎

  infixr 3 ≡⟨⟩∎-syntax
open PathReasoning using (≡⟨⟩∎-syntax) public

infixr 1 _$_
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
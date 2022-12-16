{-# OPTIONS --postfix-projections #-}

open import CubicalPlayground.Prelude hiding (_$_)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Graph using (Graph; Node; Edge; Diag; _$_; _<$>_)

module CubicalPlayground.LoopyChain.Base where

data AdjLoop (LoopIdx : ℕ → Type) : ℕ → ℕ → Type where
  next : (n : ℕ) → AdjLoop LoopIdx n (suc n)
  loopIdx : (n : ℕ) → LoopIdx n → AdjLoop LoopIdx n n 

LoopyChainGraph : (LoopIdx : (n : ℕ) → Type) → Graph _ _
LoopyChainGraph LoopIdx .Node = ℕ
LoopyChainGraph LoopIdx .Edge m n = AdjLoop LoopIdx m n

record LoopyChain (LoopIdx : (n : ℕ) → Type) : Type₁ where
  field
    Ob : ℕ → Type
    ι : (n : ℕ) → Ob n → Ob (suc n)
    loop : (n : ℕ) → LoopIdx n → Ob n → Ob n
  
  asDiag : Diag _ (LoopyChainGraph LoopIdx)
  asDiag $ n = Ob n
  _<$>_ asDiag {m} {.(suc m)} (next .m) = ι m
  _<$>_ asDiag {m} {.m} (loopIdx .m x) = loop m x

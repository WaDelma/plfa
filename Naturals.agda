module Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Exercise `seven`
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
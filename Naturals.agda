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

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc n + m = suc (n + m)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- Exercise `+-example`
_ : 3 + 4 ≡ 7
_ : refl

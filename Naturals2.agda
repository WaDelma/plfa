module Naturals2 where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven = suc (suc (suc (suc (suc (suc (suc zero))))))

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- +-example
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩ 
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
0 * _ = 0
suc m * n = n + (m * n)

-- *-example
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
_ ^ 0 = 1
m ^ suc n = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ 0 = m
0 ∸ suc n = 0
suc m ∸ suc n = m ∸ n

-- ∸-example₁
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎
-- ∸-example₂
_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 4
  ≡⟨⟩
    0 ∸ 3
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}


data Bin : Set where
 ⟨⟩ : Bin
 _O : Bin → Bin
 _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = inc x O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    inc (⟨⟩ I O I) O
  ≡⟨⟩
    inc (⟨⟩ I O) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = 2 * (from x)
from (x I) = 2 * (from x) + 1

_ : 0 ≡ from (⟨⟩ O)
_ = refl

_ : ⟨⟩ O ≡ to 0
_ = refl

_ : 1 ≡ from (⟨⟩ I)
_ = refl

_ : ⟨⟩ I ≡ to 1
_ = refl

_ : 2 ≡ from (⟨⟩ I O)
_ = refl

_ : ⟨⟩ I O ≡ to 2
_ = refl

_ : 3 ≡ from (⟨⟩ I I)
_ = refl

_ : ⟨⟩ I I ≡ to 3
_ = refl

_ : 4 ≡ from (⟨⟩ I O O)
_ = refl

_ : ⟨⟩ I O O ≡ to 4
_ = refl


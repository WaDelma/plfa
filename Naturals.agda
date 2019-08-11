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
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    3 + 3
  ≡⟨⟩
    6
  ∎

-- Exercise *-example
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
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

-- Exercise _^_
_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n  = m ∸ n

-- Exercise ∸-examples
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

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 n) = x1 n
inc (x1 n) = x0 inc n

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ =
  begin
    inc (x1 x1 x0 x1 nil)
  ≡⟨⟩
   x0 inc (x1 x0 x1 nil)
  ≡⟨⟩
   x0 x0 inc (x0 x1 nil)
  ≡⟨⟩
   x0 x0 x1 x1 nil
  ∎

_ : inc (x0 nil) ≡ x1 nil
_ =
  begin
    inc (x0 nil)
  ≡⟨⟩
    x1 nil
  ∎

_ : inc (x1 nil) ≡ x0 x1 nil
_ =
  begin
    inc (x1 nil)
  ≡⟨⟩
    x0 (inc nil)
  ∎

_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ =
  begin
    inc (x0 x1 nil)
  ≡⟨⟩
    x1 x1 nil
  ∎

_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ =
  begin
    inc (x1 x1 nil)
  ≡⟨⟩
    x0 inc (x1 nil)
  ≡⟨⟩
    x0 x0 (inc nil)
  ≡⟨⟩
    x0 x0 x1 nil
  ∎

_ : inc (x0 x0 x1 nil) ≡ x1 x0 x1 nil
_ =
  begin
    inc (x0 x0 x1 nil)
  ≡⟨⟩
    x1 x0 x1 nil
  ∎


to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

from' : Bin → ℕ → ℕ
from' nil p = 0
from' (x0 n) p = from' n (suc p)
from' (x1 n) p = 2 ^ p + from' n (suc p)

from : Bin → ℕ
from n = from' n 0

_ : to 0 ≡ x0 nil
_ =
  begin
    to 0
  ≡⟨⟩
    x0 nil
  ∎

_ : from (x0 nil) ≡ 0
_ =
  begin
    from (x0 nil)
  ≡⟨⟩
    from' (x0 nil) 0
  ≡⟨⟩
    from' nil 1
  ≡⟨⟩
    0
  ∎

_ : to 1 ≡ x1 nil
_ =
  begin
    to 1
  ≡⟨⟩
    inc (to 0)
  ≡⟨⟩
    inc (x0 nil)
  ≡⟨⟩
    x1 nil
  ∎

_ : from (x1 nil) ≡ 1
_ =
  begin
    from (x1 nil)
  ≡⟨⟩
    from' (x1 nil) 0
  ≡⟨⟩
    2 ^ 0 + from' nil 1
  ≡⟨⟩
    1 + from' nil 1
  ≡⟨⟩
    1 + 0
  ≡⟨⟩
    1
  ∎

_ : to 2 ≡ x0 x1 nil
_ =
  begin
    to 2
  ≡⟨⟩
    inc (to 1)
  ≡⟨⟩
    inc (inc (to 0))
  ≡⟨⟩
    inc (inc (x0 nil))
  ≡⟨⟩
    inc (x1 nil)
  ≡⟨⟩
    x0 (inc nil)
  ≡⟨⟩
    x0 x1 nil
  ∎

_ : from (x0 x1 nil) ≡ 2
_ =
  begin
    from (x0 x1 nil)
  ≡⟨⟩
    from' (x0 x1 nil) 0
  ≡⟨⟩
    from' (x1 nil) 1
  ≡⟨⟩
    2 ^ 1 + from' nil 2
  ≡⟨⟩
    2 ^ 1 + 0
  ≡⟨⟩
    2
  ∎

_ : to 3 ≡ x1 x1 nil
_ =
  begin
    to 3
  ≡⟨⟩
    inc (to 2)
  ≡⟨⟩
    inc (inc (to 1))
  ≡⟨⟩
    inc (inc (inc (to 0)))
  ≡⟨⟩
    inc (inc (inc (x0 nil)))
  ≡⟨⟩
    inc (inc (x1 nil))
  ≡⟨⟩
    inc (x0 (inc nil))
  ≡⟨⟩
    inc (x0 x1 nil)
  ≡⟨⟩
    x1 x1 nil
  ∎

_ : from (x1 x1 nil) ≡ 3
_ =
  begin
    from (x1 x1 nil)
  ≡⟨⟩
    from' (x1 x1 nil) 0
  ≡⟨⟩
    2 ^ 0 + from' (x1 nil) 1
  ≡⟨⟩
    1 + from' (x1 nil) 1
  ≡⟨⟩
    1 + 2 ^ 1 + from' nil 2
  ≡⟨⟩
    1 + 2 ^ 1 + 0
  ≡⟨⟩
    1 + 2 + 0
  ≡⟨⟩
    1 + 2
  ≡⟨⟩
    3
  ∎

_ : to 4 ≡ x0 x0 x1 nil
_ =
  begin
    to 4
  ≡⟨⟩
    inc (to 3)
  ≡⟨⟩
    inc (inc (to 2))
  ≡⟨⟩
    inc (inc (inc (to 1)))
  ≡⟨⟩
    inc (inc (inc (inc (to 0))))
  ≡⟨⟩
    inc (inc (inc (inc (x0 nil))))
  ≡⟨⟩
    inc (inc (inc (x1 nil)))
  ≡⟨⟩
    inc (inc (x0 (inc nil)))
  ≡⟨⟩
    inc (inc (x0 x1 nil))
  ≡⟨⟩
    inc (x1 x1 nil)
  ≡⟨⟩
    x0 (inc (x1 nil))
  ≡⟨⟩
    x0 x0 (inc nil)
  ≡⟨⟩
    x0 x0 x1 nil
  ∎

_ : from (x0 x0 x1 nil) ≡ 4
_ =
  begin
    from (x0 x0 x1 nil)
  ≡⟨⟩
    from' (x0 x0 x1 nil) 0
  ≡⟨⟩
    from' (x0 x1 nil) 1
  ≡⟨⟩
    from' (x1 nil) 2
  ≡⟨⟩
    2 ^ 2 + from' nil 3
  ≡⟨⟩
    2 ^ 2 + 0
  ≡⟨⟩
    4 + 0
  ≡⟨⟩
    4
  ∎

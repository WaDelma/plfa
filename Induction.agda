module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Exercise operators
--
-- Power set of any set (Boolean ring) has two associative and commutative operators which distribute:
-- Symmetric difference (the power set is the neutral element) and union (the empty set is the neutral element).
--
-- The operator of free monoid (aka list) has neutral element (empty list, mempty) and it associates, but doesn't commute.

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p)⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-identityʳ n) ⟩
    n + zero
  ∎
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎
{- +-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
   suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    uc n + m
  ∎-}

-- Exercise finite-|-assoc
-- Nope.

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Exercise +-swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

-- Exercise *-distrib-+
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
  | +-assoc p (m * p) (n * p) = refl

prev-cong : ∀ { m n : ℕ } → suc m ≡ suc n → m ≡ n
prev-cong refl = refl

+-rev-congˡ : ∀ (n m p : ℕ) → p + n ≡ p + m → n ≡ m
+-rev-congˡ n m zero refl = refl
+-rev-congˡ n m (suc p) q
 rewrite +-rev-congˡ n m p (prev-cong q) = refl

-- Exercise *-assoc
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
  | *-assoc m n p = refl

-- Exercise *-comm
n*0=0 : ∀ (m : ℕ) → m * zero ≡ zero
n*0=0 zero = refl
n*0=0 (suc m)
  rewrite n*0=0 m = refl

*-defnˡ : ∀ (m n : ℕ) → n * suc m ≡ n + n * m
*-defnˡ m zero = refl
*-defnˡ m (suc n)
  rewrite sym (+-assoc n m (n * m))
  | +-comm n m
  | +-assoc m n (n * m)
  | sym (*-defnˡ m n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n
  rewrite n*0=0 n = refl
*-comm (suc m) n
  rewrite *-defnˡ m n
  | *-comm m n = refl

-- Exercise 0∸n≡0
∸-identity : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-identity zero = refl
∸-identity (suc n) = refl

-- Exercise ∸-|-assoc
∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero zero p = refl
∸-|-assoc zero (suc n) zero = refl
∸-|-assoc zero (suc n) (suc p) = refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p
  rewrite ∸-|-assoc m n p = refl

-- Exercise +*^
1^n=1 : ∀ (n : ℕ) → 1 ^ n ≡ 1
1^n=1 zero = refl
1^n=1 (suc n)
  rewrite +-identityʳ (1 ^ n)
  | 1^n=1 n = refl

0^sucn=1 : ∀ (n : ℕ) → 0 ^ (suc n) ≡ 0
0^sucn=1 n = refl

*-identity : ∀ (n : ℕ) → n * 1 ≡ n
*-identity zero = refl
*-identity (suc n)
 rewrite *-identity n = refl

^-+-*-assoc : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-+-*-assoc m n zero
  rewrite +-identityʳ n
  | *-identity (m ^ n) = refl
^-+-*-assoc m n (suc p)
  rewrite +-comm n (suc p)
  | sym (*-assoc (m ^ n) m (m ^ p))
  | *-comm (m ^ n) m
  | *-assoc m (m ^ n) (m ^ p)
  | +-comm p n 
  | ^-+-*-assoc m n p = refl

*-^-assoc : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
*-^-assoc m n zero = refl
*-^-assoc m n (suc p)
  rewrite sym (*-assoc (m * (m ^ p)) n (n ^ p))
  | *-assoc m (m ^ p) n
  | *-comm (m ^ p) n
  | sym (*-assoc m n (m ^ p))
  | *-assoc (m * n) (m ^ p) (n ^ p)
  | *-^-assoc m n p = refl

^-*-assoc : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^-*-assoc m n zero
  rewrite n*0=0 n = refl
^-*-assoc m n (suc p)
  rewrite *-comm n (suc p)
  | ^-+-*-assoc m n (p * n)
  | *-comm p n
  | ^-*-assoc m n p = refl

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = inc n O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ 
from ⟨⟩ = 0
from (x O) = 2 * from x
from (x I) = 1 + 2 * from x

-- Bin-ℕ-iso : ∀ (x : Bin) → to (from x) ≡ x
-- has no inhabitant because binary number with trailing zeroes maps to one without them


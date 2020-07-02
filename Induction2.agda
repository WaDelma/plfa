module Induction2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = begin
    (suc m + n) + p
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + 0 ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n
  rewrite +-suc m n
          = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero
  rewrite +-identityʳ m
          = refl
+-comm m (suc n)
  rewrite +-suc m n
          = cong suc (+-comm m n)

+-rearrange-ind : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange-ind m n p zero
  rewrite +-identityʳ p
        | +-identityʳ (m + (n + p))
        = +-assoc m n p
+-rearrange-ind m n p (suc q)
  rewrite +-suc p q
        | +-suc (m + n) (p + q)
        | +-suc (m + (n + p)) q
        = cong suc (+-rearrange-ind m n p q)

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-rearrange' : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange' m n p q
  rewrite +-assoc m n (p + q)
        | cong (m +_) (sym (+-assoc n p q))
        | sym (+-assoc m (n + p) q)
        = refl

-- Exercise +-swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite sym (+-assoc m n p)
        | +-comm m n
        | +-assoc n m p
        = refl



-- Exercise *-distrib-+
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m zero p
  rewrite +-identityʳ m
        | +-identityʳ (m * p)
        = refl
*-distrib-+ m (suc n) p
  rewrite +-suc m n
        | *-distrib-+ m n p
        | sym (+-assoc (m * p) p (n * p))
        | +-comm (m * p) p
        | +-assoc p (m * p) (n * p)
        = refl
        
-- Exercise *-assoc
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite sym (*-assoc m n p)
        | *-distrib-+ n (m * n) p
        = refl

-- Exercise *-comm
*-identityʳ : ∀ (m : ℕ) → m * 0 ≡ 0
*-identityʳ zero = refl
*-identityʳ (suc m) = *-identityʳ m

*-suc : ∀ (m n : ℕ) → (m * suc n) ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n
  rewrite *-suc m n
        | sym (+-assoc n m (m * n))
        | +-comm n m
        | +-assoc m n (m * n)
        = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n
  rewrite *-identityʳ n
        = refl
*-comm (suc m) n
  rewrite *-comm m n
        | *-suc n m
        = refl

-- Exercise 0∸n≡0
0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

-- Exercise ∸-+-assoc
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p = 0∸n≡0 p
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

-- Exercise +*^

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p
  rewrite +-identityʳ (m ^ p)
        = refl
^-distribˡ-+-* m (suc n) p
  rewrite *-assoc m (m ^ n) (m ^ p)
        = cong (m *_) (^-distribˡ-+-* m n p)

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite ^-distribʳ-* m n p
        | *-assoc m n ((m ^ p) * (n ^ p))
        | sym (*-assoc n (m ^ p) (n ^ p))
        | *-comm n (m ^ p)
        | *-assoc (m ^ p) n (n ^ p)
        | sym (*-assoc m (m ^ p) (n * (n ^ p)))  = refl

1^n≡1 : ∀ (n : ℕ) → 1 ^ n ≡ 1
1^n≡1 zero = refl
1^n≡1 (suc n)
  rewrite +-identityʳ (1 ^ n)
        = 1^n≡1 n

^-*-assoc : (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p = 1^n≡1 p
^-*-assoc m (suc n) p
  rewrite ^-distribʳ-* m (m ^ n) p
        | ^-distribˡ-+-* m p (n * p)
        | ^-*-assoc m n p  = refl

-- Exercise Bin-laws

data Bin : Set where
 ⟨⟩ : Bin
 _O : Bin → Bin
 _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = 2 * (from x)
from (x I) = 2 * (from x) + 1

suc≡+1 : ∀ (n : ℕ) → n + 1 ≡ suc n
suc≡+1 zero = refl
suc≡+1 (suc n) = cong suc (suc≡+1 n)

fi≡sf : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
fi≡sf ⟨⟩ = refl
fi≡sf (b O)
  rewrite +-identityʳ (from b)
        = suc≡+1 (from b + from b)
fi≡sf (b I)
  rewrite +-identityʳ (from (inc b))
        | +-identityʳ (from b)
        | +-assoc (from b) (from b) 1
        | suc≡+1 (from b)
        | fi≡sf b = refl

-- Counter example for `to (from b) ≡ b` is ⟨⟩
ft≡ : ∀ (n : ℕ) → from (to n) ≡ n
ft≡ zero = refl
ft≡ (suc n)
  rewrite fi≡sf (to n)
        | ft≡ n
        = refl

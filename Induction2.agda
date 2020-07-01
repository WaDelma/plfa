module Induction2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

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

*-suc : ∀ (m n : ℕ) → (n * suc m) ≡ n + (n * m)
*-suc m zero = refl
*-suc m (suc n) = {!!}

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n
  rewrite *-identityʳ n
        = refl
*-comm (suc m) n
  rewrite *-comm m n
        | *-suc m n
        = refl

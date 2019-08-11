module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Exercise operators
--
-- Power set of any set (Boolean ring) has two associative and commutative operators which distribute:
-- Symmetric difference (the power set is the neutral element) and union (the empty set is the neutral element).
--
-- The operator of free monoid (aka list) has neutral element (empty list, mempty) and it associates, but doesn't commute.




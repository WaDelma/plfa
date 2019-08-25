module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

-- Exercise orderings
-- Preorder that's not partial order: Category with two objects and one morphism both directions
-- Partial order that is not total order: Power set of a two element set and subset operator

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Exercise ≤-antisym-cases
-- z≤n s≤s case doesn't happen because first implies that m is zero and second that m is non-zero
-- s≤s z≤n case doesn't happen because first implies that n is non-zero and second that n is zero

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...   | forward m≤n = forward (s≤s m≤n)
...   | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n
  rewrite +-comm m p
  | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise *-mono-≤
*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n
  rewrite *-comm m p
  | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

-- Exercise <-trans

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- Exercise trichotomy

data Trichotomy (m n : ℕ): Set where
  less : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  more : n < m → Trichotomy m n

cong-trichotomy : ∀ {m n : ℕ} → Trichotomy m n → Trichotomy (suc m) (suc n)
cong-trichotomy t with t
...  | less m<n = less (s<s m<n)
...  | eq m≡n =  eq (cong suc m≡n)
...  | more n<m = more (s<s n<m)

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eq refl
trichotomy zero (suc n) = less z<s
trichotomy (suc m) zero = more z<s
trichotomy (suc m) (suc n) = cong-trichotomy (trichotomy m n)

-- Exercise +-mono-<
+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n
  rewrite +-comm m p
  | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Exercise ≤-iff-<
inv-s<s : ∀ {m n : ℕ} → suc m < suc n → m < n
inv-s<s (s<s m<n) = m<n

≤-implies-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-implies-< {zero} {zero} ()
≤-implies-< {zero} {suc n} sm≤n = z<s
≤-implies-< {suc m} {zero} ()
≤-implies-< {suc m} {suc n} sm≤n = s<s (≤-implies-< (inv-s≤s sm≤n))

<-implies-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-implies-≤ {zero} {zero} ()
<-implies-≤ {zero} {suc n} m<n = s≤s z≤n
<-implies-≤ {suc m} {zero} ()
<-implies-≤ {suc m} {suc n} m<n = s≤s (<-implies-≤ (inv-s<s m<n))

<-weaken : ∀ {m n : ℕ} → m < n → m < suc n
<-weaken z<s = z<s
<-weaken (s<s m<n) = s<s (<-weaken m<n)

-- Exercise <-trans-revisited
<-trans' : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans' m<s n<p = ≤-implies-< (≤-trans (<-implies-≤ (<-weaken m<s)) (<-implies-≤ n<p))

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

-- Exercise o+o≡e
+-comm-odd : ∀ {m n : ℕ} → odd (m + n) → odd (n + m)
+-comm-odd {zero} {n} on = o+e≡o on zero
+-comm-odd {suc m} {n} omn
  rewrite +-comm n (suc m) = omn

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {suc m} {n} (suc em) on  = suc (+-comm-odd {n} {m} (o+e≡o on em))

-- Exercise Bin-predicates

open import plfa.Induction using (Bin; x1_; x0_; nil; inc; to; from)

data One : Bin → Set where
  one : One (x1 nil)
  a0_ : ∀ {x : Bin} → One x → One (x0 x)
  a1_ : ∀ {x : Bin} → One x → One (x1 x)
  

data Can : Bin → Set where
  zero : Can (x0 nil)
  one : ∀ {x : Bin} → One x → Can x

inc-preserves-one : ∀ {x : Bin} → One x → One (inc x)
inc-preserves-one {.(x1 nil)} one = a0 one
inc-preserves-one {.(x0 _)} (a0 ox) = a1 ox
inc-preserves-one {.(x1 _)} (a1 ox) = a0 (inc-preserves-one ox)

inc-preserves-can : ∀ {x : Bin} → Can x → Can (inc x)
inc-preserves-can zero =  one one
inc-preserves-can (one ox) = one (inc-preserves-one ox)

can-to : ∀ (n : ℕ) → Can (to n)
can-to zero = zero
can-to (suc n) = inc-preserves-can (can-to n)

asd : ∀ {x : Bin} → One x → x0 to (from x) ≡ to (from (x0 x))
one-to-from : ∀ {x : Bin} → One x → to (from x) ≡ x

asd one = refl
asd (a0 ox) 
  rewrite one-to-from (a0 ox)
  | one-to-from (a0 a0 ox) = refl
asd {x} (a1 ox) -- = {!!}
  rewrite one-to-from ox = {!!}
--  rewrite one-to-from (a1 ox)
--  | one-to-from (a1 a1 ox) = {!!}

one-to-from one = refl
one-to-from (a0 ox) = {!cong x0_ (one-to-from ox)!}
one-to-from (a1 ox) = {!!}

can-iso : ∀ {x : Bin} → Can x → to (from x) ≡ x
can-iso zero = refl
can-iso (one ox) = one-to-from ox

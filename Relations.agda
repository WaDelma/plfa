module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; *-comm)

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
+-monoʳ-< : ∀ {p q : ℕ} → ∀(n : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p<q = p<q
+-monoʳ-< (suc n) p<q = s<s (+-monoʳ-< n p<q)

+-monoˡ-< : ∀ {m n : ℕ} → ∀(p : ℕ) → m < n → m + p < n + p
+-monoˡ-< {m} {n} p m<n rewrite +-comm m p
 | +-comm n p = +-monoʳ-< p m<n

+-mono-< : ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q
+-mono-< {m} {n} {p} {q}  m<n p<q = <-trans (+-monoˡ-< p m<n) (+-monoʳ-< n p<q)

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

open import plfa.Induction using (Bin; _I; _O; ⟨⟩; inc; to; from)

data One : Bin → Set where
  one : One (⟨⟩ I)
  aO : ∀ {x : Bin} → One x → One (x O)
  aI : ∀ {x : Bin} → One x → One (x I)
  

data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  one : ∀ {x : Bin} → One x → Can x

inc-preserves-one : ∀ {x : Bin} → One x → One (inc x)
inc-preserves-one {.(⟨⟩ I)} one = aO one
inc-preserves-one {.(_ O)} (aO ox) = aI ox
inc-preserves-one {.(_ I)} (aI ox) = aO (inc-preserves-one ox)

inc-preserves-can : ∀ {x : Bin} → Can x → Can (inc x)
inc-preserves-can zero =  one one
inc-preserves-can (one ox) = one (inc-preserves-one ox)

can-to : ∀ {n : ℕ} → Can (to n)
can-to {zero} = zero
can-to {suc n} = inc-preserves-can (can-to {n})

one-to : ∀(n : ℕ) → One (to (suc n))
one-to zero = one
one-to (suc n) = inc-preserves-one (one-to n)

2x : ∀{x : Bin} → One x → Bin
2x {⟨⟩} ()
2x {x O} (aO ox) = x O O
2x {.⟨⟩ I} one = ⟨⟩ I O
2x {x I} (aI ox) = x I O

one-2x : ∀{x : Bin} → ∀(ox : One x) → One (2x ox)
one-2x {.(⟨⟩ I)} one = aO one
one-2x {.(_ O)} (aO ox) = aO (aO ox)
one-2x {.(_ I)} (aI ox) = aO (aI ox)

n+n≡2n : ∀(n : ℕ) → n + n ≡ 2 * n
n+n≡2n n rewrite +-identityʳ n = refl

2x-inc : ∀{x : Bin} → ∀(ox : One x) → inc (inc (2x ox)) ≡ 2x (inc-preserves-one ox)
2x-inc one = refl
2x-inc (aO ox) = refl
2x-inc (aI ox) = refl

2n≡2x : ∀ (n : ℕ) → to (2 * (suc n)) ≡ 2x (one-to n)
2n≡2x zero = refl
2n≡2x (suc n)
 rewrite sym (2x-inc (one-to n))
 | sym (2n≡2x n)
 | +-identityʳ n
 | +-comm n (suc (suc n))
 | +-comm n (suc n) = refl

inc≡+1 : ∀ (n : ℕ) → to (n + 1) ≡ inc (to n)
inc≡+1 zero = refl
inc≡+1 (suc n) rewrite inc≡+1 n = refl

<-weaken-+ : ∀{n m : ℕ} → ∀(o : ℕ) → n < m → n < o + m
<-weaken-+ zero x = x
<-weaken-+ (suc o) z<s = z<s
<-weaken-+ (suc o) (s<s x) = s<s (<-weaken-+ o (<-weaken x))

one-suc : ∀{x : Bin} → One x → 0 < from x
one-suc one = z<s
one-suc (aO {x} ox) rewrite +-identityʳ (from x) = let as = one-suc ox in +-mono-< as as
one-suc (aI {x} ox) = z<s

open import Data.Product using (Σ; _,_; Σ-syntax)

+-mono-≡ : ∀ {m n p q : ℕ} → m ≡ n → p ≡ q → m + p ≡ n + q
+-mono-≡ refl refl = refl

-- asd : ∀ (x : Bin) → One x → Σ[ n ∈ ℕ ] (from x ≡ suc n)
-- lel : ∀ (x : Bin) → ∀ (ox : One x) → from x + (from x + zero) ≡ suc (Σ.proj₁ (asd x ox) + Σ.proj₁ (asd x ox))

-- lel x ox rewrite +-identityʳ (from x)
--  | +-identityʳ (Σ.proj₁ (asd x ox)) = let z = Σ.proj₂ (asd x ox) in {!+-mono-≡ z z!}

-- asd ⟨⟩ ()
-- asd (x O) (aO ox) = ( Σ.proj₁ (asd x ox) + Σ.proj₁ (asd x ox), lel x ox )
-- asd (.⟨⟩ I) one = ( zero , refl )
-- asd (x I) (aI ox) = {!!}

n+ss≡s+s : ∀(n m : ℕ) → n + suc (suc n) ≡ suc n + suc n
n+ss≡s+s n m rewrite +-comm n (suc n)
 | +-comm n (suc (suc n))= refl

n+n≡2x : ∀{n : ℕ} → 0 < n → to (n + n) ≡ to n O
n+n≡2x {.1} (z<s {zero}) = refl
n+n≡2x {.(suc (suc n))} (z<s {suc n}) rewrite n+ss≡s+s n n
 | n+n≡2x {suc n} z<s  = refl

one-iso-O : ∀ {x : Bin} → One x → to (from (x O)) ≡ (to (from x)) O
one-iso-I : ∀ {x : Bin} → One x → to (from (x I)) ≡ (to (from x)) I

one-iso-O one = refl
one-iso-O (aO {x} ox)
 rewrite +-identityʳ (from x + from x)
 | +-identityʳ (from x)
 | +-identityʳ (from x + from x)
 | +-identityʳ (from x)
 | n+n≡2x (+-mono-< (one-suc ox) (one-suc ox)) = refl
one-iso-O (aI {x} ox) = {!!}
 -- rewrite one-iso-I ox
 -- | +-identityʳ (from x) = {!!}

one-iso-I one = refl
one-iso-I (aO ox) rewrite one-iso-O ox = {!!}
one-iso-I (aI {x} ox)
 rewrite +-identityʳ (from x + from x)
 | +-identityʳ (from x)
 | +-comm (from x + from x) (suc (from x + from x + 0))
 | +-identityʳ (from x + from x)
 | n+n≡2x (+-mono-< (one-suc ox) (one-suc ox)) = refl

can-iso : ∀ {x : Bin} → Can x → to (from x) ≡ x
can-iso zero = refl
can-iso (one one) = refl
can-iso (one (aO ox)) rewrite one-iso-O ox | can-iso (one ox) = refl
can-iso (one (aI ox)) rewrite one-iso-I ox | can-iso (one ox) = refl

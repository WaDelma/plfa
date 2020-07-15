module Isomorphism2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc; +-assoc)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

_⍮_ : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
f ⍮ g = λ a → g (f a)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ 0 = m
m +′ suc n = suc (m +′ n)

same-app : ∀(m n : ℕ) → m +′ n ≡ m + n
same-app zero zero = refl
same-app (suc m) zero rewrite +-identityʳ m = refl
same-app m (suc n) rewrite +-suc m n = cong suc (same-app m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
 ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g


infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
to ≃-refl x = x
from ≃-refl y = y
from∘to ≃-refl x = refl
to∘from ≃-refl y = refl

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym a≃b = record
 { to = from a≃b
 ; from = to a≃b
 ; from∘to = to∘from a≃b
 ; to∘from = from∘to a≃b
 }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans a≃b b≃c = record
  { to = to a≃b ⍮ to b≃c
  ; from = from a≃b ∘ from b≃c
  ; from∘to = λ x →
    begin
      from a≃b (from b≃c (to b≃c (to a≃b x)))
    ≡⟨ cong (from a≃b) (from∘to b≃c (to a≃b x)) ⟩
      from a≃b (to a≃b x)
    ≡⟨ from∘to a≃b x ⟩
      x
    ∎
  ; to∘from = λ y → trans (cong (to b≃c) (to∘from a≃b (from b≃c y))) (to∘from b≃c y)
  }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }
     
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → to A≲B ≡ from B≲A
  → from A≲B ≡ to B≲A
  → A ≃ B
≲-antisym A≲B B≲A t≡f f≡t = record
  { to = to A≲B
  ; from = from A≲B
  ; from∘to = from∘to A≲B 
  ; to∘from = λ y →
    begin
      to A≲B (from A≲B y)
    ≡⟨ cong (to A≲B) (cong-app f≡t y) ⟩
      to A≲B (to B≲A y)
    ≡⟨ cong-app t≡f (to B≲A y) ⟩
      from B≲A (to B≲A y)
    ≡⟨ from∘to B≲A y ⟩
      y
    ∎ 
  }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercise ≃-implies-≲
≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B = record
  { to = to A≃B
  ; from = from A≃B
  ; from∘to = from∘to A≃B
  }

-- Exercise _⇔_

record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record
  { to = λ a → a
  ; from = λ a → a
  }
open _⇔_

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B = record { to = from A⇔B ; from = to A⇔B }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C = record
  { to = to A⇔B ⍮ to B⇔C
  ; from = from A⇔B ∘ from B⇔C
  }

data Bin : Set where
 ⟨⟩ : Bin
 _O : Bin → Bin
 _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to' : ℕ → Bin
to' zero = ⟨⟩ O
to' (suc x) = inc (to' x)

from' : Bin → ℕ
from' ⟨⟩ = 0
from' (x O) = 2 * (from' x)
from' (x I) = 2 * (from' x) + 1

suc≡+1 : ∀ (n : ℕ) → n + 1 ≡ suc n
suc≡+1 zero = refl
suc≡+1 (suc n) = cong suc (suc≡+1 n)

fi≡sf : ∀ (b : Bin) → from' (inc b) ≡ suc (from' b)
fi≡sf ⟨⟩ = refl
fi≡sf (b O)
  rewrite +-identityʳ (from' b)
        = suc≡+1 (from' b + from' b)
fi≡sf (b I)
  rewrite +-identityʳ (from' (inc b))
        | +-identityʳ (from' b)
        | +-assoc (from' b) (from' b) 1
        | suc≡+1 (from' b)
        | fi≡sf b = refl
        
ft≡ : ∀ (n : ℕ) → from' (to' n) ≡ n
ft≡ zero = refl
ft≡ (suc n)
  rewrite fi≡sf (to' n)
        | ft≡ n
        = refl

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin = record
  { to = to'
  ; from = from'
  ; from∘to = ft≡
  }

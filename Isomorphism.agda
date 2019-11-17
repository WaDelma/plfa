module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

postulate
  extensionality : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_


≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
 record
   { to      = λ{x → x}
   ; from    = λ{y → y}
   ; from∘to = λ{x → refl}
   ; to∘from = λ{y → refl}
   }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym a≃b =
  record
    { to      = from a≃b
    ; from    = to a≃b
    ; from∘to = to∘from a≃b
    ; to∘from = from∘to a≃b
    }

∘-assoc : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {f : A → B} {g : B → C} {h : C → D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc {f = f} {g} {h} = begin
    (h ∘ g) ∘ f
  ≡⟨⟩
    (λ x → (h ∘ g) (f x))
  ≡⟨⟩
    (λ x → h (g (f x)))
  ≡⟨⟩
    (λ x → h ((g ∘ f) x) )
  ≡⟨⟩
    (h ∘ (g ∘ f))
  ∎

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans a≃b b≃c =
  record
    { to = to b≃c ∘ to a≃b
    ; from = from a≃b ∘ from b≃c
    ; from∘to = λ x → begin
        (from a≃b ∘ from b≃c) ((to b≃c ∘ to a≃b) x)
      ≡⟨⟩
        {!((from a≃b ∘ from b≃c) ∘ (to b≃c ∘ to a≃b)) x!}
    ; to∘from = λ y → {!!}
    }
    

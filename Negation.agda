module Negation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap; [_,_]′)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Isomorphism2 using (_≃_; _≲_; extensionality)
open import Relations using (_<_; z<s; s<s)
open import Function using (_∘_)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀{A : Set} → A → ¬ A → ⊥
¬-elim a ¬a = ¬a a

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro = ¬-elim

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬A = λ a → ¬¬¬A (¬¬-intro a)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b a = ¬-elim (f a) ¬b

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {n : ℕ} → 0 ≢ suc n
peano ()

absurd : ∀ {A : Set} → ⊥ → A
absurd ()

id : ⊥ → ⊥
id bot = absurd bot

-- Exercise <-irreflexive
<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive = λ{ (s<s n) → <-irreflexive n}

-- Exercise trichotomy

trichotomy : ∀ {m n : ℕ} →
  (  (m < n) × ¬ (m ≡ n) × ¬ (n < m)) ⊎
  (¬ (m < n) ×   (m ≡ n) × ¬ (n < m)) ⊎
  (¬ (m < n) × ¬ (m ≡ n) ×   (n < m))
trichotomy {zero} {zero} = inj₂ (inj₁
      ( (λ ())
      , refl
      , λ ()
      )
   )
trichotomy {zero} {suc n} = inj₁
  ( z<s
  , (λ ())
  , λ ()
  )
trichotomy {suc m} {zero} = inj₂ (inj₂
    ( (λ ())
    , (λ ())
    , z<s
    )
  )
trichotomy {suc m} {suc n} with trichotomy {m} {n}
... | inj₁ (f , s , t) = inj₁
  ( s<s f
  , (λ{ refl → s refl})
  , λ{ (s<s x) → t x}
  )
... | inj₂ (inj₁ (f , s , t)) = inj₂ (inj₁
    ( (λ{ (s<s x) → f x})
    , cong suc s
    , λ{ (s<s x) → t x}
    )
  )
... | inj₂ (inj₂ (f , s , t)) = inj₂ (inj₂
    ( (λ{ (s<s x) → f x})
    , (λ{ refl → s refl})
    , s<s t
    )
  )

-- Exercise ⊎-dual-×
→-distrib-⊎ : ∀ {A B C : Set} → ((A ⊎ B) → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to = λ f →
    ( (λ a → f (inj₁ a))
    , (λ b → f (inj₂ b))
    )
  ; from = λ
    { ( f , g ) (inj₁ a) → f a
    ; ( f , g ) (inj₂ b) → g b
    }
  ; from∘to = λ f → extensionality λ
    { (inj₁ a) → refl
    ; (inj₂ b) → refl
    }
  ; to∘from = λ{ ( f , g ) → refl}
  }

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

{- ×-dual-⊎ : ∀ {A B : Set} → ((¬ A) ⊎ (¬ B)) ≲ (¬ (A × B))
×-dual-⊎ = record
  { to = λ
    { (inj₁ ¬a) (a , b) → ¬a a
    ; (inj₂ ¬b) (a , b) → ¬b b
    }
  ; from = λ ¬a×b → inj₁ λ a → {!!}
  ; from∘to = {!!}
  } -}


-- (A × B) → C ≃ A → C ⊎ B → C

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ f → f (inj₂ λ a → f (inj₁ a))

-- Exercise Classical
em-dne : (f : ∀ {A : Set} → A ⊎ ¬ A) → ∀ {A : Set} → ¬ ¬ A → A
em-dne f {A} ¬¬a = let
    em = f {A}
    g : A ⊎ ¬ A → A
    g = λ
      { (inj₁ a) → a
      ; (inj₂ ¬a) → absurd (¬¬a ¬a)
      }
  in g em

dne-em : (f : ∀ {A : Set} → ¬ ¬ A → A) → ∀ {A : Set} → A ⊎ ¬ A
dne-em f {A} = f em-irrefutable

dne-pl : (f : ∀ {A : Set} → A ⊎ ¬ A) → ∀ {A B : Set} → ((A → B) → A) → A
dne-pl f x = let
    a = {!!}
  in {!!}


pl-dne : (f : ∀ {A B : Set} → ((A → B) → A) → A) → ∀ {A : Set} → ¬ ¬ A → A
pl-dne f {A} ¬¬a = let
    a = {!!}
  in {!!}

{- dne-pl : ∀ {A : Set} → (¬ ¬ A → A) → (f : ∀ {B : Set} → ((A → B) → A)) → A
dne-pl {A} x f = let
    ¬¬A : ¬ ¬ A
    ¬¬A = λ{¬a → ¬a (f ¬a) }
  in x ¬¬A -}

em-iad : (f : ∀ {A B : Set} →  A ⊎ ¬ A → (A → B)) →  {A B : Set} →  ¬ A ⊎ B
em-iad f {A} {B} = let
    a = f {A} {B}
    b : {!!}
    b = {!!}
  in {!!}
-- em-iad (inj₁ b) f = inj₂ (f b)
-- em-iad (inj₂ ¬a) f = inj₁ ¬a

iad-em : ∀ {A : Set} → (f : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B) → A ⊎ ¬ A 
iad-em {A} f = swap (f λ x → x)

dm-em : ∀ {A : Set} (f : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B) → A ⊎ ¬ A
dm-em {A} f = let
    param : ¬ (¬ A × ¬ (¬ A))
    param = λ{ (¬a , ¬¬a) → absurd (¬¬a ¬a)}
  in f param

dm-pl : ∀ {A : Set} (f : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B) → ¬ ¬ A → A
dm-pl {A} f ¬¬a = let
    proj : ¬ A × ¬ A → ¬ A
    proj = λ x → proj₁ x
    param = (contraposition proj) ¬¬a
    id = λ x → x
    collapse : A ⊎ A → A
    collapse = [ id , id ]′
  in collapse (f param)


module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Isomorphism2 using (_≃_; extensionality)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (<-cmp; +-identityʳ; +-comm)
open import Relation.Binary.Core renaming (Tri to Trich)

-- Exercise ∀-distrib-×
∀-distrib-× : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ f →
    ⟨ (λ a → proj₁ (f a))
    , (λ a → proj₂ (f a))
    ⟩
  ; from = λ{ ⟨ f , g ⟩ a → ⟨ f a , g a ⟩}
  ; from∘to = λ f → refl
  ; to∘from = λ f → refl
  }
-- This one doesn't need extensionality where →-distrib-× needed it. :O

-- Exercise ⊎∀-implies-∀⊎
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) a = inj₁ (f a)
⊎∀-implies-∀⊎ (inj₂ f) a = inj₂ (f a)

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  z : Even zero
  even : ∀ {n : ℕ} →  Odd n → Even (suc n)

data Odd where
  odd : ∀ {n : ℕ} →  Even n → Odd (suc n)

ℕ-even-odd : ∀ (n : ℕ) → Even n ⊎ Odd n
ℕ-even-odd zero = inj₁ z
ℕ-even-odd (suc zero) = inj₂ (odd z)
ℕ-even-odd (suc (suc n)) = let
    p₀ = ℕ-even-odd n
    p₁ : Even n ⊎ Odd n → Even (suc (suc n)) ⊎ Odd (suc (suc n))
    p₁ = λ
      { (inj₁ e) → inj₁ (even (odd e))
      ; (inj₂ o) → inj₂ (odd (even o))
      }
  in p₁ p₀

even-odd-⊥ : ∀ {n : ℕ} → Even n → Odd n → ⊥
even-odd-⊥ {suc n} (even o) (odd e) = even-odd-⊥ e o


∀⊎-¬implies-⊎∀ : ¬(∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x))
∀⊎-¬implies-⊎∀ = λ f → let
     p₀ = f {ℕ} {λ n → Even n} {λ n → Odd n} ℕ-even-odd
     p₁ : ((n : ℕ) → Even n) ⊎ ((n : ℕ) → Odd n) → ⊥
     p₁ = λ
       { (inj₁ f) → even-odd-⊥ (f 1) (odd z)
       ; (inj₂ f) → even-odd-⊥ z (f 0)
       }
   in p₁ p₀

-- Exercise ∀-×
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (a : A) → B a} → (∀ (a : A) → f a ≡ g a) → f ≡ g

-- Exercise ∀-×
tri-∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
tri-∀-× = record
  { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
  ; from = λ
    { ⟨ a , ⟨ b , c ⟩ ⟩ aa → a
    ; ⟨ a , ⟨ b , c ⟩ ⟩ bb → b
    ; ⟨ a , ⟨ b , c ⟩ ⟩ cc → c
    }
  ; from∘to = λ x → ∀-extensionality λ
    { aa → refl
    ; bb → refl
    ; cc → refl
    }
  ; to∘from = λ y → refl
  }

data ∑ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∑ A B

∑-syntax = ∑
infix 2 ∑-syntax
syntax ∑-syntax A (λ x → B) = ∑[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} → {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f ⟨ a , b ⟩ = f a b

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to = ∃-elim
  ; from = λ{f a b → f ⟨ a , b ⟩}
  ; from∘to = λ f → refl
  ; to∘from = λ g → extensionality λ{ ⟨ a , b ⟩ → refl }
  }

-- Exercise ∃-distrib-⊎
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to = λ
    { ⟨ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩
    ; ⟨ a , inj₂ c ⟩ → inj₂ ⟨ a , c ⟩
    }
  ; from = λ
    { (inj₁ ⟨ a , b ⟩) → ⟨ a , inj₁ b ⟩
    ; (inj₂ ⟨ a , c ⟩) → ⟨ a , inj₂ c ⟩
    }
  ; from∘to = λ
    { ⟨ a , inj₁ b ⟩ → refl
    ; ⟨ a , inj₂ c ⟩ → refl
    }
  ; to∘from = λ
    { (inj₁ ⟨ a , b ⟩) → refl
    ; (inj₂ ⟨ a , c ⟩) → refl
    }
  }

-- ∃×-implies-×∃
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ b , c ⟩ ⟩ = ⟨ ⟨ a , b ⟩ , ⟨ a , c ⟩ ⟩

×∃-¬implies-∃× : ¬(∀ {A : Set} {B C : A → Set} → (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x))
×∃-¬implies-∃× f = let
    p₀ = f {ℕ} {Even} {Odd} ⟨ ⟨ 0 , z ⟩ , ⟨ 1 , odd z ⟩ ⟩
    p₁ : ∃[ x ] (Even x × Odd x) → ⊥
    p₁ = λ{ ⟨ n , ⟨ o , e ⟩ ⟩ → even-odd-⊥ o e }
  in p₁ p₀

-- Exercise ∃-⊎
tri-∃-⊎ : ∀ {B : Tri → Set} → (∃[ x ] B x) ≃ B aa ⊎ B bb ⊎ B cc
tri-∃-⊎ = record
  { to = λ
    { ⟨ aa , a ⟩ → inj₁ a
    ; ⟨ bb , b ⟩ → inj₂ (inj₁ b)
    ; ⟨ cc , c ⟩ → inj₂ (inj₂ c)
    }
  ; from = λ
    { (inj₁ a) → ⟨ aa , a ⟩
    ; (inj₂ (inj₁ b)) → ⟨ bb , b ⟩
    ; (inj₂ (inj₂ c)) → ⟨ cc , c ⟩
    }
  ; from∘to = λ
    { ⟨ aa , a ⟩ → refl
    ; ⟨ bb , b ⟩ → refl
    ; ⟨ cc , c ⟩ → refl
    }
  ; to∘from = λ
    { (inj₁ a) → refl
    ; (inj₂ (inj₁ b)) → refl
    ; (inj₂ (inj₂ c)) → refl
    }
  }

even-∃ : ∀ {n : ℕ} → Even n → ∃[ m ] (m * 2 ≡ n)
odd-∃ : ∀ {n : ℕ} → Odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ z = ⟨ 0 , refl ⟩
even-∃ (even o) with odd-∃ o
...                | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd e) with even-∃ e
...              | ⟨ m , refl ⟩ = ⟨ m , refl ⟩ 

_mod_ : ∀ (n m : ℕ) → ℕ
n mod m with <-cmp n m
n mod m | tri< a ¬b ¬c = n
n mod m | tri≈ ¬a b ¬c = 0
n mod m | tri> ¬a ¬b c = n ∸ m

∃-even : ∀ {n : ℕ} → ∃[ m ] (m * 2 ≡ n) → Even n
∃-odd : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → Odd n

∃-even ⟨ zero , refl ⟩ = z
∃-even ⟨ suc m , refl ⟩ = even (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd (∃-even ⟨ m , refl ⟩)

-- Exercise ∃-even-odd

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → Even n
∃-odd′ : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → Odd n

∃-even′ ⟨ zero , refl ⟩ = z
∃-even′ ⟨ suc x , refl ⟩ = {!!}

∃-odd′ ⟨ m , refl ⟩ rewrite +-identityʳ m | +-comm (m + m) 1 = odd {!∃-even′ refl!}

module Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Isomorphism2 using (_≃_; _≲_; _⇔_; extensionality)
open Isomorphism2.≃-Reasoning
open _⇔_

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩}
  ; from = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩}
  ; from∘to = λ{ ⟨ x , y ⟩ → refl}
  ; to∘from = λ{ ⟨ x , y ⟩ → refl}
  } 

×-assoc : ∀ {A B C : Set} → (A × B) × C → A × (B × C)
×-assoc ⟨ ⟨ x , y ⟩ , z ⟩ = ⟨ x , ⟨ y , z ⟩ ⟩

-- Exercise ⇔≃×
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to = λ x → ⟨ to x , from x ⟩
  ; from = λ x → record { to = proj₁ x ; from = proj₂ x }
  ; from∘to = λ x → refl
  ; to∘from = λ{ ⟨ x , y ⟩ → refl}
  }


data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record
  { to = λ{ ⟨ _ , a ⟩ → a}
  ; from = λ{ a → ⟨ tt , a ⟩}
  ; from∘to = λ{ ⟨ tt , a ⟩ → refl}
  ; to∘from = λ a → refl
  }


data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ a→c b→c (inj₁ a) = a→c a
case-⊎ a→c b→c (inj₂ b) = b→c b

infixr 1 _⊎_

-- Exercise ⊎-comm
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = λ
    { (inj₁ a) → inj₂ a
    ; (inj₂ b) → inj₁ b
    }
  ; from = λ
    { (inj₁ b) → inj₂ b
    ; (inj₂ a) → inj₁ a
    }
  ; from∘to = λ
    { (inj₁ x) → refl
    ; (inj₂ x) → refl
    }
  ; to∘from = λ
    { (inj₁ x) → refl
    ; (inj₂ x) → refl
    }
  }

-- Exercise ⊎-assoc
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to = λ
    { (inj₁ (inj₁ x)) → inj₁ x
    ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
    ; (inj₂ x) → inj₂ (inj₂ x)
    }
  ; from = λ
    { (inj₁ x) → inj₁ (inj₁ x)
    ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
    ; (inj₂ (inj₂ x)) → inj₂ x
    }
  ; from∘to = λ
    { (inj₁ (inj₁ x)) → refl
    ; (inj₁ (inj₂ x)) → refl
    ; (inj₂ x) → refl
    }
  ; to∘from = λ
    { (inj₁ x) → refl
    ; (inj₂ (inj₁ x)) → refl
    ; (inj₂ (inj₂ x)) → refl
    }
  }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Exercise ⊥-identityˡ
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = record
  { to = λ{ (inj₂ x) → x}
  ; from = inj₂
  ; from∘to = λ{ (inj₂ x) → refl}
  ; to∘from = λ y → refl
  }

-- Exercise ⊥-identityʳ
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} = ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎


→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

currying : ∀ {A B C : Set} → (A → B → C) ≃ ((A × B) → C)
currying = record
  { to = λ{ f ⟨ a , b ⟩ → f a b}
  ; from = λ g a b → g ⟨ a , b ⟩
  ; from∘to = λ f → refl
  ; to∘from = λ{ g → extensionality λ{ ⟨ a , b ⟩ → refl }}
  }

→-distrib-⊎ : ∀ {A B C : Set} → ((A ⊎ B) → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to = λ f →
    ⟨ (λ a → f (inj₁ a))
    , (λ b → f (inj₂ b))
    ⟩
  ; from = λ
    { ⟨ f , g ⟩ (inj₁ a) → f a
    ; ⟨ f , g ⟩ (inj₂ b) → g b
    }
  ; from∘to = λ f → extensionality λ
    { (inj₁ a) → refl
    ; (inj₂ b) → refl
    }
  ; to∘from = λ{ ⟨ f , g ⟩ → refl}
  }


×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to = λ
    { ⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩
    ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩
    }
  ; from = λ
    { (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩
    ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩
    }
  ; from∘to = λ
    { ⟨ inj₁ a , c ⟩ → refl
    ; ⟨ inj₂ b , c ⟩ → refl
    }
  ; to∘from = λ
    { (inj₁ ⟨ a , c ⟩) → refl
    ; (inj₂ ⟨ b , c ⟩) → refl
    }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
  { to = λ
    { (inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩
    ; (inj₂ c) → ⟨ inj₂ c , inj₂ c ⟩
    }
  ; from = λ
    { ⟨ inj₁ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩
    ; ⟨ inj₁ a , inj₂ c ⟩ → inj₂ c
    ; ⟨ inj₂ c , inj₁ b ⟩ → inj₂ c
    ; ⟨ inj₂ c , inj₂ _ ⟩ → inj₂ c
    }
  ; from∘to = λ
    { (inj₁ ⟨ a , b ⟩) → refl
    ; (inj₂ c) → refl
    }
  }

-- Exercise ⊎-weak-×
⊎-weak-× : ∀{A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

-- Exercise ⊎×-implies-×⊎
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩


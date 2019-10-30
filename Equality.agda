module plfa.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) → {u x : A} → {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ _ refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl _ = refl

subst : ∀ {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst _ refl px = px

module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _ ∎ = refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z = begin 
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

infixl 6 _+_

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) = begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

trans-≤ : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
trans-≤ z≤n _ = z≤n
trans-≤ (s≤s a≤b) (s≤s b≤c) = s≤s (trans-≤ a≤b b≤c)

module ≤-Reasoning where
  infix 1 start_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _◾

  start_ : ∀ {a b : ℕ} → a ≤ b → a ≤ b
  start a≤b = a≤b
  
  _≤⟨⟩_ : ∀ (a : ℕ) {b : ℕ} → a ≤ b → a ≤ b
  _ ≤⟨⟩ a≤b = a≤b

  _≤⟨_⟩_ : ∀ (a : ℕ) {b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  _ ≤⟨ a≤b ⟩ b≤c = trans-≤ a≤b b≤c

  _◾ : ∀ (a : ℕ) → a ≤ a
  zero ◾ = z≤n
  suc a ◾ = s≤s (a ◾)

open ≤-Reasoning

+-mono-≤ˡ : ∀ {u v x : ℕ} → u ≤ v → u + x ≤ v + x
+-mono-≤ˡ {u} {v} {zero} u≤v = start
    u + zero
  ≤⟨ {!!} ⟩
    u
  ≤⟨ u≤v ⟩
    v
  ≤⟨ {!!} ⟩
    v + zero
  ◾
+-mono-≤ˡ {u} {v} {suc x} u≤v = start u + suc x ≤⟨ {!!} ⟩ v + suc x ◾

+-mono-≤ʳ : ∀ {v x y : ℕ} → x ≤ y → v + x ≤ v + y
+-mono-≤ʳ {zero} {x} {y} x≤y = x≤y
+-mono-≤ʳ {suc v} {x} {y} x≤y = start suc (v + x) ≤⟨ {!!} ⟩ {!!}

+-mono-≤ : ∀ {u v x y : ℕ} → u ≤ v → x ≤ y → u + x ≤ v + y
+-mono-≤ {u} {v} {x} {y} u≤v x≤y = start
    u + x
  ≤⟨ +-mono-≤ˡ u≤v ⟩
    v + x
  ≤⟨ {!!} ⟩
    v + y
  ◾

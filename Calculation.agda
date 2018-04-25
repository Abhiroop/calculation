module Calculation  where

-- First order intuitionistic logic

data ⊥ : Set where                           -- absurdity

data T : Set where                           -- truth
  tt : T

data _×_ (A B : Set) : Set where             -- conjunction
  _,_ : A → B → A × B

data _⨄_ (A B : Set) : Set where             -- disjunction
  inj₁ : A → A ⨄ B
  inj₂ : B → A ⨄ B

-- A → B                                    -- implication

data ∃ {A : Set} (P : A → Set) : Set where  -- existential quantification
  _,_ : (witness : A) → P witness → ∃ P

-- (x : A) → P x  or ∀ x → P x              -- universal quantification

data _≡_ {A : Set} : A → A → Set where      -- equality
  refl : {x : A} → x ≡ x

-- Encoding "every natural number is either zero or a successor of some natural number."
-- (n : ℕ) → (n ≡ zero ⨄ ∃ (λm → n ≡ suc m))

-- Generalized Product type where the second component's type "depends" on the first component
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∘ : {A : Set} (x : A) → x ≡ x
x ∘ = refl

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

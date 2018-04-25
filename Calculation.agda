module Calculation where

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

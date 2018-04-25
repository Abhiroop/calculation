## calculation

Program calculation works by the calculus of constructive induction. Can we use Agda to calculate programs? YES!

Proving fold fusion laws:

```agda
foldr-fusion : {A B C : Set}
  (h : B → C) {f : A → B → B} {g : A → C → C} {e : B} →
    (∀ x y → h (f x y) ≡ g x (h y)) →
      ∀ xs → h (foldr f e xs) ≡ foldr g (h e) xs
foldr-fusion h {f} {g} {e} fusion-condition [ ] = refl
foldr-fusion h {f} {g} {e} fusion-condition (x :: xs) =
  h (foldr f e (x :: xs))
  ≡⟨ refl ⟩
  h (f x (foldr f e xs))
  ≡⟨ fusion-condition x (foldr f e xs) ⟩
  g x (h (foldr f e xs))
  ≡⟨ cong (g x) (foldr-fusion h fusion-condition xs) ⟩
  g x (foldr g (h e) xs)
  ≡⟨ refl ⟩
  foldr g (h e) (x :: xs) ∘

```

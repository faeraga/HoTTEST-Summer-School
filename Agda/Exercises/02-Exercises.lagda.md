# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = (inl a , inl b)
[i] (inr c) = (inr c , inr c)

[ii] : {A B C : Type} → (A ∔ C) × (B ∔ C) → (A × B) ∔ C
[ii] (inl a , inl b) = inl (a , b)
[ii] (_ , inr c) = inr c
[ii] (inr c , _) = inr c

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] f = (λ a → f (inl a)) , (λ b → f (inr b))

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] f = {!!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f ¬b a = ¬b (f a)

[fae] : {A B : Type} → ¬ (A × B) → A → ¬ B
[fae] f a b = f (a , b)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] f b = {!!}

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] p a b = p (a , b)

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] = {!!}

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] f = (λ a → pr₁ (f a)) , λ a → pr₂ (f a)
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne ¬¬¬a a = ¬¬¬a (λ ¬a → ¬a a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f = [v] ([v] f)

¬¬-functor' : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor' f ¬¬a ¬b = ¬¬a (λ a → ¬b (f a))

thing : {A B : Type} → (¬ B → ¬ A) → ¬¬ A → ¬¬ B
thing ¬b⇒¬a ¬¬a ¬b = ¬¬a (¬b⇒¬a ¬b)


¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli a⇒¬¬b ¬¬a ¬b = ¬¬a (λ a → a⇒¬¬b a ¬b)

¬¬-kleisli' : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli' = {!!}
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ b b (refl b) = id , id
```


### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false true≡false = true⇒false ⋆
 where
  true⇒false : 𝟙 → 𝟘
  true⇒false = pr₁ (bool-≡-char₁ true false true≡false)

true≢false' : ¬ (true ≡ false)
true≢false' true≡false = {!𝟙≢𝟘 (ap bool-as-type true≡false)!}
 where
  𝟙≢𝟘 : ¬ (𝟙 → 𝟘)
  𝟙≢𝟘 f = f ⋆



```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true _ = refl true
bool-≡-char₂ true false (b→b' , _) = 𝟘-elim (b→b' ⋆)
bool-≡-char₂ false true (_ , b'→b) = 𝟘-elim (b'→b ⋆)
bool-≡-char₂ false false _ = refl false
```

```agda
--bool-≡-char : (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
--bool-≡-char b b' = (bool-≡-char₁ , bool-≡-char₂)
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
--data _∔_ (A B : Type) : Type where
-- inl : A → A ∔ B
-- inr : B → A ∔ B
--
--¬_ : Type → Type
--¬ A = A → 𝟘

is-decidable' : Type → Type
is-decidable' A = A ∔ ¬ A

has-decidable-equality' : Type → Type
has-decidable-equality' X = (x y : X) → is-decidable' (x ≡ y)

has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that
```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
pr₁ (decidable-equality-char A) eq = pred , pred-is-bool-dec
 where
  dec-to-bool : {x y : A} → (x ≡ y) ∔ (x ≡ y → 𝟘) → Bool
  dec-to-bool (inl _) = true
  dec-to-bool (inr _) = false

  pred : A → A → Bool
  pred x y = dec-to-bool (eq x y)
    
  pred-x-x : {x : A} (d : is-decidable (x ≡ x)) → dec-to-bool d ≡ true
  pred-x-x (inl _) = refl true
  pred-x-x {x} (inr x≢x) = 𝟘-elim ((x≢x) (refl x))

  pred-is-bool-dec : (x y : A) → x ≡ y ⇔ (pred x y ≡ true)
  pr₁ (pred-is-bool-dec x x) (refl x) = pred-x-x (eq x x) 
  pr₂ (pred-is-bool-dec x y) p with (eq x y)
  ... | inl x=y = x=y
  
-- pr₁ of has-bool-dec is a function from A → A → Bool
-- pr₂ of has-bool-dec is the proof that that function is equivalent
-- to x ≡ y
pr₂ (decidable-equality-char A) (pred , pred-dec) x y with (pred x y)
... | true =  inl {!(eq x y)!}
... | false = inr {!!}

    
```

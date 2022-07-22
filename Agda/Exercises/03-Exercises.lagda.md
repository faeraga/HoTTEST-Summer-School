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

module 03-Exercises where

open import prelude hiding (_∼_)
```

## Part I -- Homotopies

It is often convenient to work with *pointwise equality* of functions, defined as follows.
```agda
module _ {A : Type} {B : A → Type} where
  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Type
  f ∼ g = ∀ x → f x ≡ g x
```
An element of `f ∼ g` is usually called a homotopy.

### Exercise 1 (⋆⋆)

Unsurprisingly, many properties of this type of pointwise equalities
can be inferred directly from the same operations on paths.

Try to prove reflexivity, symmetry and transitivity of `_∼_` by filling these holes.
```agda
  ∼-refl : (f : (x : A) → B x) → f ∼ f
  ∼-refl f x = refl (f x)

  ∼-inv : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  ∼-inv f g f∼g x = sym (f∼g x)

  ∼-inv' : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  ∼-inv' f g f∼g x = (f∼g x)⁻¹

  ∼-concat : (f g h : (x : A) → B x) → f ∼ g → g ∼ h → f ∼ h
  ∼-concat f g h f∼g g∼h x = trans (f∼g x) (g∼h x)

  ∼-concat' : (f g h : (x : A) → B x) → f ∼ g → g ∼ h → f ∼ h
  ∼-concat' f g h f~g g~h x = f~g x ∙ g~h x
  
  infix 0 _∼_
```

## Part II -- Isomorphisms

A function `f : A → B` is called a *bijection* if there is a function `g : B → A` in the opposite direction such that `g ∘ f ∼ id` and `f ∘ g ∼ id`. Recall that `_∼_` is [pointwise equality](identity-type.lagda.md) and that `id` is the [identity function](products.lagda.md). This means that we can convert back and forth between the types `A` and `B` landing at the same element we started with, either from `A` or from `B`. In this case, we say that the types `A` and `B` are *isomorphic*, and we write `A ≅ B`. Bijections are also called type *isomorphisms*. We can define these concepts in Agda using [sum types](sums.lagda.md) or [records](https://agda.readthedocs.io/en/latest/language/record-types.html). We will adopt the latter, but we include both definitions for the sake of illustration.
Recall that we [defined](general-notation.lagda.md) the domain of a function `f : A → B` to be `A` and its codomain to be `B`.

We adopt this definition of isomorphisms using records.
```agda
record is-bijection {A B : Type} (f : A → B) : Type where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_
```

### Exercise 2 (⋆)

Reformulate the same definition using Sigma-types.
```agda

record Σ' {A : Type } (B : A → Type) : Type  where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁

Sigma' : (A : Type) (B : A → Type) → Type
Sigma' A B = Σ {A} B

--syntax Sigma' A (λ x → b) = Σ' x ꞉ A , b

--  η       : inverse ∘ f ∼ id
--  ε       : f ∘ inverse ∼ id

is-bijection' : {A B : Type} → (A → B) → Type
is-bijection' {A} {B} f =
  Sigma (B → A) λ inverse →
  Sigma (inverse ∘ f ∼ id) λ η →
  (f ∘ inverse ∼ id)

_≅'_ : Type → Type → Type
A ≅' B = Sigma (A → B) λ f → is-bijection' f
```
The definition with `Σ` is probably more intuitive, but, as discussed above,
the definition with a record is often easier to work with,
because we can easily extract the components of the definitions using the names of the fields.
It also often allows Agda to infer more types, and to give us more sensible goals in the
interactive development of Agda programs and proofs.

Notice that `inverse` plays the role of `g`.
The reason we use `inverse` is that then we can use the word
`inverse` to extract the inverse of a bijection.
Similarly we use `bijection` for `f`, as we can use the word
`bijection` to extract the bijection from a record.

This type can be defined to be `𝟙 ∔ 𝟙` using the coproduct,
but we give a direct definition which will allow us to discuss some relationships between the various type formers of Basic MLTT.

```agda
data 𝟚 : Type where
 𝟎 𝟏 : 𝟚
```

### Exercise 3 (⋆⋆)

Prove that 𝟚 and Bool are isomorphic

```agda
Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f false = 𝟎
  f true  = 𝟏

  f⁻¹ : 𝟚 → Bool
  f⁻¹ 𝟎 = false
  f⁻¹ 𝟏 = true

  f-is-bijection : is-bijection f
  f-is-bijection = record {
    inverse = f⁻¹ ;
    η = λ { true → refl true ; false → refl false } ;
    ε = λ { 𝟎 → refl 𝟎 ; 𝟏 → refl 𝟏 } }
```


## Part III - Finite Types

In the last HoTT Exercises we encountered two definitions of the finite types.
Here we prove that they are isomorphic.
Note that `zero` was called `pt` and suc `i` on the HoTT exercise sheet.

```agda
data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)

```

### Exercise 4 (⋆)

Prove the elimination principle of `Fin`.
```agda
Fin-elim : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f {n} zero = a
Fin-elim A a f (suc k) = f k Ak
 where
  Ak : A k
  Ak = Fin-elim A a f k
```

We give the other definition of the finite types and introduce some notation.

```agda


Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr
```

### Exercise 5 (⋆⋆⋆)

Prove that `Fin n` and `Fin' n` are isomorphic for every `n`.

```agda
Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f {n} ; bijectivity = f-is-bijection {n} }
 where
  f : {n : ℕ} → Fin n → Fin' n
  f zero    = zero'
  f (suc k) = suc' (f k) 

  g : {n : ℕ} → Fin' n → Fin n
  g {suc n} (inl ⋆) = zero
  g {suc n} (inr k) = suc (g k)

  gf∼id : {n : ℕ} → g {n} ∘ f {n} ∼ id
  gf∼id zero    = refl zero
  gf∼id (suc k) =
    g (f (suc k))  ≡⟨ refl _ ⟩
    g (suc' (f k)) ≡⟨ refl _ ⟩
    suc (g (f k))  ≡⟨ ap suc (gf∼id k) ⟩
    suc k                                      ∎

  fg∼id : {n : ℕ} → f {n} ∘ g {n} ∼ id
  fg∼id {suc n} (inl ⋆) = refl (inl ⋆)
  fg∼id {suc n} (inr k) =
    f (g (suc' k))  ≡⟨ refl _ ⟩
    f (suc (g k))   ≡⟨ refl _ ⟩
    suc' (f (g k))  ≡⟨ ap suc' (fg∼id k) ⟩
    suc' k                                      ∎

  f-is-bijection : {n : ℕ} → is-bijection (f)
  f-is-bijection {n} = record { inverse = g ; η = gf∼id ; ε = fg∼id {n} }
```

## Part IV -- minimal elements in the natural numbers

In this section we establish some definitions which are needed to state and prove the well-ordering
principle of the natural numbers.

### Exercise 6 (⋆)

Give the recursive definition of the less than or equals relation on the natural numbers.

```agda
_≤₁_ : ℕ → ℕ → Type
0     ≤₁ y     = 𝟙
suc x ≤₁ 0     = 𝟘
suc x ≤₁ suc y = x ≤₁ y
```

### Exercise 7 (⋆)

Given a type family `P` over the naturals, a lower bound `n` is a natural number such that
for all other naturals `m`, we have that if `P(m)` holds, then`n ≤₁ m`.
Translate this definition into HoTT.

```agda
is-lower-bound : (P : ℕ → Type) (n : ℕ) → Type
is-lower-bound P n = (m : ℕ) → P m → n ≤₁ m 

is-minimal-element : (P : ℕ → Type) (n : ℕ) → Type
is-minimal-element P n = (P n) × is-lower-bound P n
```

We define the type of minimal elements of a type family over the naturals.
```agda
minimal-element : (P : ℕ → Type) → Type
minimal-element P = Sigma ℕ (is-minimal-element P)
```

### Exercise 8 (⋆)

Prove that all numbers are at least as large as zero.
```agda
leq-zero : (n : ℕ) → 0 ≤₁ n
leq-zero n = ⋆
```


## Part V -- The well-ordering principle of ℕ

Classically, the well-ordering principle states that every non-empty set
of natural numbers has a least element.

In HoTT, such subsets can be translated as decidable type family.
Recall the definition of decidability:
```agda
open import decidability
  using (is-decidable; is-decidable-predicate)
```

The well-ordering principle reads
```agda
Well-ordering-principle = (P : ℕ → Type) → (d : is-decidable-predicate P) → (n : ℕ) → P n → minimal-element P

Well-ordering-principle' = (P : ℕ → Type) → (d : is-decidable-predicate P) → (Sigma ℕ (λ n → P n)) → minimal-element P
```


We shall prove this statement via induction on `n`.
In order to make the proof more readable, we first prove two lemmas.

### Exercise 9 (🌶)

What is the statement of `is-minimal-element-suc`
under the Curry-Howard interpretation?
Prove this lemma.

For all decidable predicates `P` on the natural numbers, all m such that P accepts (suc m), all proofs that m is a lower bound for such integers, and all proofs that (P 0) is empty, we can produce a proof that (suc m) is a lower bound for P.

If P is a decidable predicate on ℕ and n=m is the smallest value for which P(n+1) and P(0) is false, then n=m+1 is the smallest value for which P(n)

```agda
is-minimal-element-suc :
  {P : ℕ → Type} → ¬ (P 0) →
  (m : ℕ) → P (suc m) →
  is-lower-bound (λ x → P (suc x)) m →
  is-lower-bound P (suc m)
is-minimal-element-suc ¬p0 _ _ _ 0 p0 = ¬p0 p0
is-minimal-element-suc _ 0 _ _ (suc _) _ = ⋆
is-minimal-element-suc _ (suc m) _ suc-suc-m-is-lower-bound (suc n) p-n = suc-suc-m-is-lower-bound n p-n
```

### Exercise 10 (🌶)

What is the statement of `well-ordering-principle-suc`
under the Curry-Howard interpretation?
Prove this lemma.

If P is a predicate on the natural numbers, and P' = n → P (n+1) has a minimal element,
then P has a minimal element.

```agda
well-ordering-principle-suc :
  (P : ℕ → Type) → (n : ℕ) → P (suc n) → is-decidable (P 0) →
  minimal-element (λ m → P (suc m)) → minimal-element P
well-ordering-principle-suc P _ _ (inl p0) _  = 0 , p0 , (λ m _ → ⋆)
well-ordering-principle-suc P _ _ (inr ¬p0) (m , p'-m , m-is-min) = (suc m , p'-m , suc-m-is-min)
 where
  suc-m-is-min : is-lower-bound P (suc m)
  suc-m-is-min zero p0 = ¬p0 p0
  suc-m-is-min (suc k) p-suc-k = m-is-min k p-suc-k
```

### Exercise 11 (🌶)

Use the previous two lemmas to prove the well-ordering principle
```agda
well-ordering-principle : (P : ℕ → Type) → (d : is-decidable-predicate P) → (n : ℕ) → P n → minimal-element P
well-ordering-principle _ _ 0 p0 = 0 , p0 , λ _ _ → ⋆
well-ordering-principle P d (suc n) p-suc-n = P-min
 where
  P' : ℕ → Type
  P' m = P (suc m)

  d' : is-decidable-predicate P'
  d' m = d (suc m)

  P'-min : minimal-element P'
  P'-min = well-ordering-principle P' d' n p-suc-n  

  P'-min-to-P-min : minimal-element P' → minimal-element P
  P'-min-to-P-min = well-ordering-principle-suc P n p-suc-n (d 0)

  P-min = P'-min-to-P-min P'-min

```

### Exercise 12 (🌶)

Prove that the well-ordering principle returns 0 if `P 0` holds.

```agda
{-is-zero-well-ordering-principle-suc :
  (P : ℕ → Type) → is-decidable-predicate P →
  (n : ℕ) → (p : P (suc n)) → (d0 : is-decidable (P 0)) →
  (x : minimal-element (λ m → P (suc m))) (p0 : P 0) →
  (pr₁ (well-ordering-principle-suc P n p d0 x)) ≡ 0
is-zero-well-ordering-principle-suc P d n p (inl p0) x q0 = refl 0
is-zero-well-ordering-principle-suc P d n p (inr np0) x q0 = 𝟘-elim (np0 q0)-}

is-zero-well-ordering-principle-suc :
  (P : ℕ → Type) → is-decidable-predicate P →
  (n : ℕ) → (p : P (suc n)) → (d0 : is-decidable (P 0)) →
  (x : minimal-element (λ m → P (suc m))) → (p0 : P 0) →
  (pr₁ (well-ordering-principle-suc P n p d0 x)) ≡ 0
is-zero-well-ordering-principle-suc P d n p-suc-n (inl p0) x q0 = refl 0
is-zero-well-ordering-principle-suc P d n p-suc-n (inr ¬p0) x p0 = 𝟘-nondep-elim (¬p0 p0)

is-zero-well-ordering-principle :
  (P : ℕ → Type) (d : is-decidable-predicate P) →
  (n : ℕ) → (pn : P n) →
  P 0 →
  pr₁ (well-ordering-principle P d n pn) ≡ 0
is-zero-well-ordering-principle P d 0 p p0 = refl 0
is-zero-well-ordering-principle P d (suc m) pm = is-zero-well-ordering-principle-suc P d m pm (d 0) min-P'
 where
  P' : ℕ → Type
  P' n = P (suc n)

  d' : is-decidable-predicate P'
  d' n = d (suc n)
  
  min-P' : minimal-element P'
  min-P' = well-ordering-principle P' d' m pm 
```

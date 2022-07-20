```agda
{-# OPTIONS --without-K --safe #-}

module lec2 where

open import lecture1 hiding (𝟘 ; 𝟙 ; D)

data 𝟘 : Type where

𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()

¬_ : Type → Type
¬ A = A → 𝟘

infix 1000 ¬_

𝟘-nondep-elim : {B : Type} → 𝟘 → B
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}


is-empty : Type → Type
is-empty A = A → 𝟘


𝟘-is-empty'' : is-empty 𝟘
𝟘-is-empty'' x = x

𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = 𝟘-nondep-elim

𝟘-is-empty' : is-empty 𝟘
𝟘-is-empty' = id


--data 𝟙 : Type where
--  ⋆ : 𝟙

-- Unit type
record 𝟙 : Type where
 constructor
  ⋆

open 𝟙 public

𝟙-is-nonempty : ¬ is-empty 𝟙
𝟙-is-nonempty f  = f ⋆

𝟙-elim : {A : 𝟙 → Type}
  → A ⋆
  → (x : 𝟙) → A x
𝟙-elim a ⋆ = a


data 𝟚 : Type where
  𝟎 𝟏 : 𝟚

𝟚-elim : {A : 𝟚 → Type}
  → A 𝟎
  → A 𝟏
  → (x : 𝟚) → A x
𝟚-elim a₀ a₁ 𝟎 = a₀
𝟚-elim a₀ a₁ 𝟏 = {!!}

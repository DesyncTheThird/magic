module Intro where


------------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed.Base

open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation.Base
    renaming ( ∥_∥₁ to ∥_∥ 
             ; ∣_∣₁ to ∣_∣
             ; squash₁ to squash 
             )

open import Cubical.HITs.PropositionalTruncation.Properties

import Cubical.Foundations.Pointed.Homogeneous as hg


------------------------------------------------------------------------------






















------------------------------------------------------------------------------
{-

A pointed type (A,a) is *homogeneous* if, for every other point b : A,
there is an equality of pointed types (A, a) ≡ (A, B).

-}

isHomogeneous : ∀ {ℓ} → Pointed ℓ → Type (ℓ-suc ℓ)
isHomogeneous {ℓ} (A , x) = ∀ y → Path (Pointed ℓ) (A , x) (A , y)




isDiscrete : ∀ {ℓ} → Type ℓ → Type ℓ
isDiscrete A = (x y : A) → Dec (x ≡ y)



isDiscrete→isHomogeneous : ∀ {ℓ} → (𝔸@(A , a) : Pointed ℓ) → isDiscrete A → isHomogeneous 𝔸
isDiscrete→isHomogeneous 𝔸 = hg.isHomogeneousDiscrete {A∙ = 𝔸}
-- with p a x
-- ... | yes q = λ i → A , q i
-- ... | no q = λ i → A , {!!}

--(A , {!p a x!})



isDiscrete-ℕ : isDiscrete ℕ
isDiscrete-ℕ zero zero = yes refl
isDiscrete-ℕ zero (suc b) = no znots
isDiscrete-ℕ (suc a) zero = no snotz
isDiscrete-ℕ (suc a) (suc b) with isDiscrete-ℕ a b
... | yes  p = yes (cong suc p)
... | no  ¬p = no (λ x → ¬p (injSuc x))




isHomogeneous-ℕ : isHomogeneous (ℕ , 0)
isHomogeneous-ℕ = isDiscrete→isHomogeneous (ℕ , 0) isDiscrete-ℕ



module Recover {ℓ} (𝔸@(A , a) : Pointed ℓ) (h : isHomogeneous 𝔸) where

  -- We send points of the truncation to the type of pointed types equivalent to (A , a)

  toEquivPtd : ∥ A ∥ → Σ[ 𝔹 ∈ Pointed ℓ ] (A , a) ≡ 𝔹
  toEquivPtd = rec isPropSingl (λ x → (A , x) , h x)


  private
    P : ∥ A ∥ → Pointed ℓ
    P tx = (toEquivPtd tx) .fst

  -- P ∣x∣ is definitionally equal to (A,x) for any x : ∥A∥
  private
    check : ∀ x → P ∣ x ∣ ≡ (A , x)
    check x = refl

  -- that is, we can recover terms out of a truncation!



  recover : ∀ (tx : ∥ A ∥) → fst (P tx)
  recover tx = pt (P tx)

  recover∣∣ : ∀ (x : A) → recover ∣ x ∣ ≡ x
  recover∣∣ x = refl



  private
    -- notice that the following typechecks because `fst (P ∣ x ∣)` is definitionally equal to A, but
    -- `recover : ∥ A ∥ → A` does not, because `fst (P tx)` is not definitionally equal to A.
    f : A → A
    f = recover ∘ ∣_∣

    -- we might wonder if (cong recover (squash ∣ x ∣ ∣ y ∣)) therefore has type x ≡ y
    -- but `fst (P (squash ∣ x ∣ ∣ y ∣ i))`` is not A
    recover-squash : ∀ x y → -- x ≡ y -- this raises an error
                             PathP (λ i → typ (P (squash ∣ x ∣ ∣ y ∣ i))) x y
    recover-squash x y = cong recover (squash ∣ x ∣ ∣ y ∣)


private
  open Recover (ℕ , 0) (isDiscrete→isHomogeneous (ℕ , 0) discreteℕ)

  -- this module does not expose `hidden`, so we can't access it from outside
  module _ where
    private
      hidden : ℕ
      hidden = 17

    ∣hidden∣ : ∥ ℕ ∥
    ∣hidden∣ = ∣ hidden ∣

  -- but we can still recover the value:
  test : recover ∣hidden∣ ≡ 17
  test = refl

  -- Finally, note that `recover` does not use the proof of A being homogeneous to compute this hidden value

------------------------------------------------------------------------------

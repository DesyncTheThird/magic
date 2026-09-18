module Intro where


------------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed.Base

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

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

------------------------------------------------------------------------------





















------------------------------------------------------------------------------

{-

A type A is *decidable* if A + ¬A is inhabited.

A type A is *discrete* if all of its equality types are decidable.

-}

isDiscrete : ∀ {ℓ} → Type ℓ → Type ℓ
isDiscrete A = (x y : A) → Dec (x ≡ y)



isDiscreteBool : isDiscrete Bool
isDiscreteBool false false = yes refl
isDiscreteBool false true = no false≢true
isDiscreteBool true false = no true≢false
isDiscreteBool true true = yes refl



isDiscreteℕ : isDiscrete ℕ
isDiscreteℕ zero zero = yes refl
isDiscreteℕ zero (suc b) = no znots
isDiscreteℕ (suc a) zero = no snotz
isDiscreteℕ (suc a) (suc b) with isDiscreteℕ a b
... | yes  p = yes (cong suc p)
... | no  ¬p = no (λ x → ¬p (injSuc x))

------------------------------------------------------------------------------






















------------------------------------------------------------------------------

-- Discrete sets are homogeneous:

isDiscrete→isHomogeneous : ∀ {ℓ} → (𝔸@(A , a) : Pointed ℓ) → isDiscrete A → isHomogeneous 𝔸
isDiscrete→isHomogeneous 𝔸 = hg.isHomogeneousDiscrete {A∙ = 𝔸}

isHomogeneous-ℕ : isHomogeneous (ℕ , 0)
isHomogeneous-ℕ = isDiscrete→isHomogeneous (ℕ , 0) isDiscreteℕ

------------------------------------------------------------------------------









------------------------------------------------------------------------------

{-

For any pointed type X, the type of pointed types equivalent to X is contractible,
with centre of contraction given by (X, refl), with path from any other pointed path
to X given by construction.

-}

pointedEqContra : ∀ {ℓ} → (X : Pointed ℓ) → isContr (Σ[ Y ∈ Pointed ℓ ] X ≡ Y)
pointedEqContra X = (X , refl) , (λ (Y , ϕ) → ΣPathP (ϕ , λ i j → ϕ (i ∧ j)))

------------------------------------------------------------------------------



-- ======================================================================== --
-- The magic begins
-- ======================================================================== --

-- Fix a homogeneous type 𝔸 = (A, a).

module Recover {ℓ} (𝔸@(A , a) : Pointed ℓ) (h : isHomogeneous 𝔸) where

  -- This function sends points of the truncation to the type of pointed types equivalent to (A , a)
  -- i.e. the type of pairs (𝔹,ϕ), where 𝔹 is a pointed type and ϕ is a proof of (A,a) ≡ 𝔹.
  toEquivPtd : ∥ A ∥ → Σ[ 𝔹 ∈ Pointed ℓ ] (A , a) ≡ 𝔹
  toEquivPtd = rec (isContr→isProp (pointedEqContra (A , a))) λ a → (A , a) , h a


  private
    -- We can define a pointed type family over the truncation by sending each truncated point tx
    -- to the type 𝔹 from above.
    P : ∥ A ∥ → Pointed ℓ
    P tx = (toEquivPtd tx) .fst

  -- Then, P ∣x∣ is definitionally equal to (A,x) for any x : ∥A∥;
  private
    check : ∀ x → P ∣ x ∣ ≡ (A , x)
    check x = refl

  -- that is, we can recover terms out of a truncation!



  recover : ∀ (tx : ∥ A ∥) → fst (P tx)
  recover tx = (P tx) .snd

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

------------------------------------------------------------------------------









------------------------------------------------------------------------------
{-

We start with some truncated data. Imagine in place of ℕ some very complicated type where we
did a lot of work to produce a term hidden : ∥ ℕ ∥ in a way where the truncation is essential.

-}

private
  open Recover (ℕ , 0) (isDiscrete→isHomogeneous (ℕ , 0) discreteℕ)

  module _ where
    -- this module does not export `hidden`, so we can't access it from outside
    private
      hidden : ℕ
      hidden = 17

    -- we only export the value wrapped by the truncation:
    ∣hidden∣ : ∥ ℕ ∥
    ∣hidden∣ = ∣ hidden ∣

  -- but we can still recover the value:
  not-hidden : ℕ
  not-hidden = recover ∣hidden∣
  
  _ : not-hidden ≡ 17
  _ = refl
  
  

  -- Finally, note that `recover` does not use the proof of A being homogeneous to compute this hidden value

------------------------------------------------------------------------------




















------------------------------------------------------------------------------

-- David Wärn's construction
{- A simple, general version of Kraus' magic trick, to recover truncated data. -}


-- Let A be an arbitrary type (not necessarily homogeneous).
module _ {ℓ : Level} {A : Type ℓ} where

-- Define a family of contractible types over A using contractibility of singletons.
  fam : ∥ A ∥₁ → TypeOfHLevel ℓ 0
  fam ∣ a ∣ = singl a , isContrSingl a
  fam (squash a b i) = isPropHContr (fam a) (fam b) i

-- Now we can seemingly factor the identity map on A through the propositional truncation.
-- The idea is that fam ∣ a ∣ is a contractible type, so we can take its centre of contraction.
-- This centre of contraction is (a , refl). So the first component gives us back a.
  magic : A → A
  magic = fst ∘ fst ∘ str ∘ fam ∘ ∣_∣

-- magic computes as expected.
  magic≡id : (a : A) → magic a ≡ a
  magic≡id _ = refl

------------------------------------------------------------------------------









------------------------------------------------------------------------------
{-

Again, suppose ℕ is some very complicated type and we want to access the value
hidden : ∥ ℕ ∥ in the truncation.

-}

private
  module _ where
    private
      hidden : ℕ
      hidden = 23

    ∣hidden'∣ : ∥ ℕ ∥
    ∣hidden'∣ = ∣ hidden ∣


  -- Now we have un-truncated data!
  not-hidden' : ℕ
  not-hidden' = fst (fst (str (fam ∣hidden'∣)))
  
  _ : not-hidden' ≡ 23
  _ = refl

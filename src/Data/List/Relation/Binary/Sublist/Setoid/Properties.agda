-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the setoid sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; _⇒_; _Preserves_⟶_)

module Data.List.Relation.Binary.Sublist.Setoid.Properties
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base hiding (_∷ʳ_)
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  as HeteroProperties
import Data.List.Membership.Setoid as SetoidMembership
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Linked using (Linked)
import Data.List.Relation.Unary.Unique.Setoid as SetoidUniqueness
import Data.Maybe.Relation.Unary.All as Maybe
open import Data.Nat using (_≤_; _≥_; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_; proj₁; proj₂)
open import Function
open import Function.Bijection   using (_⤖_)
open import Function.Equivalence using (_⇔_)
open import Level using (Level)
open import Relation.Binary using (Rel; _Respects_; _Respects₂_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable; Irrelevant)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬?)

open Setoid S using (_≈_; sym; trans) renaming (Carrier to A)
open SetoidEquality S using (_≋_; ≋-refl)
open SetoidSublist S hiding (map)
open SetoidMembership S using (_∈_)
open SetoidUniqueness S using (Unique)

private
  variable
    p r : Level

------------------------------------------------------------------------
-- Injectivity of constructors
------------------------------------------------------------------------

module _ {xs ys : List A} {pxs qxs : xs ⊆ ys} where

  ∷-injectiveˡ : ∀ {x y} {px qx : x ≈ y} → px ∷ pxs ≡ qx ∷ qxs → px ≡ qx
  ∷-injectiveˡ = HeteroProperties.∷-injectiveˡ

  ∷-injectiveʳ : ∀ {x y} {px qx : x ≈ y} → px ∷ pxs ≡ qx ∷ qxs → pxs ≡ qxs
  ∷-injectiveʳ = HeteroProperties.∷-injectiveʳ

  ∷ʳ-injective : ∀ {y} → y ∷ʳ pxs ≡ y ∷ʳ qxs → pxs ≡ qxs
  ∷ʳ-injective = HeteroProperties.∷ʳ-injective

------------------------------------------------------------------------
-- Predicates preserved by _⊆_
------------------------------------------------------------------------

module _ {P : Pred A p} (P-resp-≈ : P Respects _≈_) where

  Any-resp-⊆ : (Any P) Respects _⊆_
  Any-resp-⊆ (y   ∷ʳ xs⊆ys) pxs         = there (Any-resp-⊆ xs⊆ys pxs)
  Any-resp-⊆ (x≈y ∷  xs⊆ys) (here  px)  = here (P-resp-≈ x≈y px)
  Any-resp-⊆ (x≈y ∷  xs⊆ys) (there pxs) = there (Any-resp-⊆ xs⊆ys pxs)

  All-resp-⊇ : (All P) Respects _⊇_
  All-resp-⊇ []             pys        = pys
  All-resp-⊇ (y   ∷ʳ xs⊆ys) (_  ∷ pys) = All-resp-⊇ xs⊆ys pys
  All-resp-⊇ (x≈y ∷  xs⊆ys) (py ∷ pys) =
    P-resp-≈ (sym x≈y) py ∷ (All-resp-⊇ xs⊆ys pys)

module _ {R : Rel A r} (R-resp-≈ : R Respects₂ _≈_) where

  AllPairs-resp-⊇ : (AllPairs R) Respects _⊇_
  AllPairs-resp-⊇ []             pys        = pys
  AllPairs-resp-⊇ (y   ∷ʳ xs⊆ys) (_  ∷ pys) = AllPairs-resp-⊇ xs⊆ys pys
  AllPairs-resp-⊇ (x≈y ∷  xs⊆ys) (py ∷ pys) =
    All-resp-⊇ (proj₁ R-resp-≈) xs⊆ys
      (All.map (proj₂ R-resp-≈ (sym x≈y)) py) ∷
    AllPairs-resp-⊇ xs⊆ys pys

∈-resp-⊆ : ∀ {v} → (v ∈_) Respects _⊆_
∈-resp-⊆ = Any-resp-⊆ (flip trans)

-- This should be simplified using ≉-resp-≈ once #783 is merged
Unique-resp-⊇ : Unique Respects _⊇_
Unique-resp-⊇ = AllPairs-resp-⊇
  ((λ z≈y x≉z x≈y → x≉z (trans x≈y (sym z≈y))) ,
  (λ x≈y x≉z y≈z → x≉z (trans x≈y y≈z)))

------------------------------------------------------------------------
-- Various functions' outputs are sublists
------------------------------------------------------------------------

tail-⊆ : ∀ xs → Maybe.All (_⊆ xs) (tail xs)
tail-⊆ xs = HeteroProperties.tail-Sublist ⊆-refl

take-⊆ : ∀ n xs → take n xs ⊆ xs
take-⊆ n xs = HeteroProperties.take-Sublist n ⊆-refl

drop-⊆ : ∀ n xs → drop n xs ⊆ xs
drop-⊆ n xs = HeteroProperties.drop-Sublist n ⊆-refl

module _ {p} {P : Pred A p} (P? : Decidable P) where

  takeWhile-⊆ : ∀ xs → takeWhile P? xs ⊆ xs
  takeWhile-⊆ xs = HeteroProperties.takeWhile-Sublist P? ⊆-refl

  dropWhile-⊆ : ∀ xs → dropWhile P? xs ⊆ xs
  dropWhile-⊆ xs = HeteroProperties.dropWhile-Sublist P? ⊆-refl

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ xs = HeteroProperties.filter-Sublist P? ⊆-refl

module _ {p} {P : Pred A p} (P? : Decidable P) where

  takeWhile⊆filter : ∀ xs → takeWhile P? xs ⊆ filter P? xs
  takeWhile⊆filter xs = HeteroProperties.takeWhile-filter P? {xs} ≋-refl

  filter⊆dropWhile : ∀ xs → filter P? xs ⊆ dropWhile (¬? ∘ P?) xs
  filter⊆dropWhile xs = HeteroProperties.filter-dropWhile P? {xs} ≋-refl

------------------------------------------------------------------------
-- Various list functions are increasing wrt _⊆_
------------------------------------------------------------------------
-- We write f⁺ for the proof that `xs ⊆ ys → f xs ⊆ f ys`
-- and f⁻ for the one that `f xs ⊆ f ys → xs ⊆ ys`.

module _ {as bs : List A} where

  ∷ˡ⁻ : ∀ {a} → a ∷ as ⊆ bs → as ⊆ bs
  ∷ˡ⁻ = HeteroProperties.∷ˡ⁻

  ∷ʳ⁻ : ∀ {a b} → ¬ (a ≈ b) → a ∷ as ⊆ b ∷ bs → a ∷ as ⊆ bs
  ∷ʳ⁻ = HeteroProperties.∷ʳ⁻

  ∷⁻ : ∀ {a b} → a ∷ as ⊆ b ∷ bs → as ⊆ bs
  ∷⁻ = HeteroProperties.∷⁻

------------------------------------------------------------------------
-- map

module _ {b ℓ} (R : Setoid b ℓ) where

  open Setoid R using () renaming (Carrier to B; _≈_ to _≈′_)
  open SetoidSublist R using () renaming (_⊆_ to _⊆′_)

  map⁺ : ∀ {as bs} {f : A → B} → f Preserves _≈_ ⟶ _≈′_ →
         as ⊆ bs → map f as ⊆′ map f bs
  map⁺ {f = f} f-resp as⊆bs =
    HeteroProperties.map⁺ f f (SetoidSublist.map S f-resp as⊆bs)

------------------------------------------------------------------------
-- _++_

module _ {as bs : List A} where

  ++⁺ˡ : ∀ cs → as ⊆ bs → as ⊆ cs ++ bs
  ++⁺ˡ = HeteroProperties.++ˡ

  ++⁺ʳ : ∀ cs → as ⊆ bs → as ⊆ bs ++ cs
  ++⁺ʳ = HeteroProperties.++ʳ

  ++⁺ : ∀ {cs ds} → as ⊆ bs → cs ⊆ ds → as ++ cs ⊆ bs ++ ds
  ++⁺ = HeteroProperties.++⁺

  ++⁻ : ∀ {cs ds} → length as ≡ length bs → as ++ cs ⊆ bs ++ ds → cs ⊆ ds
  ++⁻ = HeteroProperties.++⁻

------------------------------------------------------------------------
-- take

module _  where

  take⁺ : ∀ {m n} {xs} → m ≤ n → take m xs ⊆ take n xs
  take⁺ m≤n = HeteroProperties.take⁺ m≤n ≋-refl

------------------------------------------------------------------------
-- drop

module _ {m n} {xs ys : List A} where

  drop⁺ : m ≥ n → xs ⊆ ys → drop m xs ⊆ drop n ys
  drop⁺ = HeteroProperties.drop⁺

module _ {m n} {xs : List A} where

  drop⁺-≥ : m ≥ n → drop m xs ⊆ drop n xs
  drop⁺-≥ m≥n = drop⁺ m≥n ⊆-refl

module _ {xs ys : List A} where

  drop⁺-⊆ : ∀ n → xs ⊆ ys → drop n xs ⊆ drop n ys
  drop⁺-⊆ n xs⊆ys = drop⁺ {n} ℕₚ.≤-refl xs⊆ys

------------------------------------------------------------------------
-- takeWhile / dropWhile

module _ {p q} {P : Pred A p} {Q : Pred A q}
         (P? : Decidable P) (Q? : Decidable Q) where

  takeWhile⁺ : ∀ {xs} → (∀ {a b} → a ≈ b → P a → Q b) →
               takeWhile P? xs ⊆ takeWhile Q? xs
  takeWhile⁺ {xs} P⇒Q = HeteroProperties.⊆-takeWhile-Sublist P? Q? {xs} P⇒Q ≋-refl

  dropWhile⁺ : ∀ {xs} → (∀ {a b} → a ≈ b → Q b → P a) →
               dropWhile P? xs ⊆ dropWhile Q? xs
  dropWhile⁺ {xs} P⇒Q = HeteroProperties.⊇-dropWhile-Sublist P? Q? {xs} P⇒Q ≋-refl

------------------------------------------------------------------------
-- filter

module _ {p q} {P : Pred A p} {Q : Pred A q}
         (P? : Decidable P) (Q? : Decidable Q) where

  filter⁺ : ∀ {as bs} → (∀ {a b} → a ≈ b → P a → Q b) →
            as ⊆ bs → filter P? as ⊆ filter Q? bs
  filter⁺ = HeteroProperties.⊆-filter-Sublist P? Q?

------------------------------------------------------------------------
-- reverse

module _ {as bs : List A} where

  reverseAcc⁺ : ∀ {cs ds} → as ⊆ bs → cs ⊆ ds →
                reverseAcc cs as ⊆ reverseAcc ds bs
  reverseAcc⁺ = HeteroProperties.reverseAcc⁺

  reverse⁺ : as ⊆ bs → reverse as ⊆ reverse bs
  reverse⁺ = HeteroProperties.reverse⁺

  reverse⁻ : reverse as ⊆ reverse bs → as ⊆ bs
  reverse⁻ = HeteroProperties.reverse⁻

------------------------------------------------------------------------
-- Inversion lemmas
------------------------------------------------------------------------

module _ {a b} {A : Set a} {B : Set b} {a as b bs} where

  ∷⁻¹ : a ≈ b → as ⊆ bs ⇔ a ∷ as ⊆ b ∷ bs
  ∷⁻¹ = HeteroProperties.∷⁻¹

  ∷ʳ⁻¹ : ¬ (a ≈ b) → a ∷ as ⊆ bs ⇔ a ∷ as ⊆ b ∷ bs
  ∷ʳ⁻¹ = HeteroProperties.∷ʳ⁻¹

------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------

module _ where

  length-mono-≤ : ∀ {as bs} → as ⊆ bs → length as ≤ length bs
  length-mono-≤ = HeteroProperties.length-mono-≤

------------------------------------------------------------------------
-- Conversion to and from list equality

  to-≋ : ∀ {as bs} → length as ≡ length bs → as ⊆ bs → as ≋ bs
  to-≋ = HeteroProperties.toPointwise

------------------------------------------------------------------------
-- Irrelevant special case

module _ {a b} {A : Set a} {B : Set b}  where

  []⊆-irrelevant : Irrelevant ([] ⊆_)
  []⊆-irrelevant = HeteroProperties.Sublist-[]-irrelevant

------------------------------------------------------------------------
-- (to/from)∈ is a bijection

module _ {x xs} where

  to∈-injective : ∀ {p q : [ x ] ⊆ xs} → to∈ p ≡ to∈ q → p ≡ q
  to∈-injective = HeteroProperties.toAny-injective

  from∈-injective : ∀ {p q : x ∈ xs} → from∈ p ≡ from∈ q → p ≡ q
  from∈-injective = HeteroProperties.fromAny-injective

  to∈∘from∈≗id : ∀ (p : x ∈ xs) → to∈ (from∈ p) ≡ p
  to∈∘from∈≗id = HeteroProperties.toAny∘fromAny≗id

  [x]⊆xs⤖x∈xs : ([ x ] ⊆ xs) ⤖ (x ∈ xs)
  [x]⊆xs⤖x∈xs = HeteroProperties.Sublist-[x]-bijection

module Category where

open import Relation.Binary.PropositionalEquality

record Category : Set1 where
  constructor
    makeCat
  field
    Object : Set
    Arrow : Object → Object → Set
    identity : (a : Object) → Arrow a a
    composition : {a b c : Object} → Arrow a b → Arrow b c → Arrow a c
    associativity : {a b c d : Object} → (f : Arrow a b) → (g : Arrow b c) → (h : Arrow c d) →
      composition (composition f g) h ≡ composition f (composition g h)
    unit_law_left  : {a b : Object} → (f : Arrow a b) → composition f (identity b) ≡ f
    unit_law_right : {b c : Object} → (g : Arrow b c) → composition (identity b) g ≡ g
  
open import Data.Product

record IsSemigroup {A : Set} (_∙_ : A → A → A) : Set where
  constructor
    prfSemigroup
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record IsMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  constructor
    prfMonoid
  field
    isSemigroup : IsSemigroup _∙_
    identity : (∀ x → ε ∙ x ≡ x) × (∀ x → x ∙ ε ≡ x)

  open IsSemigroup isSemigroup public

record Monoid : Set1 where
  field
    uset : Set  -- underlying set
    e    : uset -- identity element
    ∘    : uset → uset → uset
    isMonoid : IsMonoid ∘ e

record IsGroup {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  constructor
    prfGroup
  field
    isMonoid : IsMonoid _∙_ ε
    inverse  : (x : A) → Σ A (λ y → (y ∙ x ≡ ε) × (x ∙ y ≡ ε))

  open IsMonoid isMonoid public

record Group : Set1 where
  constructor
    makeGroup
  field
    uset : Set  -- underlying set
    e    : uset -- identity element
    ∘    : uset → uset → uset
    isGroup : IsGroup ∘ e

record IsAbelianGroup {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  constructor
    prfAbelianGroup
  field
    comm    : ∀ x y → x ∙ y ≡ y ∙ x
    isGroup : IsGroup _∙_ ε

  open IsGroup isGroup public
  
record AbelianGroup : Set1 where
  constructor
    makeAbelianGroup
  field
    uset : Set  -- underlying set
    e    : uset -- identity element
    ∘    : uset → uset → uset
    isAbelianGroup : IsAbelianGroup ∘ e

record IsRing {A : Set} (_∙_ _∘_ : A → A → A) (e₁ e₂ : A) : Set where
  constructor
    prfRing
  field
    dist           : ∀ x y z → (z ∘ (x ∙ y) ≡ (z ∘ x) ∙ (z ∘ y)) × ((x ∙ y) ∘ z ≡ (x ∘ z) ∙ (y ∘ z))
    isAbelianGroup : IsAbelianGroup _∙_ e₁
    isMonoid       : IsMonoid       _∘_ e₂

record Ring : Set1 where
  constructor
    makeRing
  field
    uset : Set  -- underlying set
    ∙    : uset → uset → uset
    ∘    : uset → uset → uset    
    e₁   : uset -- identity element for ∙
    e₂   : uset -- identity element for ∘ 
    isRing : IsRing ∙ ∘ e₁ e₂

record IsVecSpace (F : Set) (V : Set) (_∘_ : F → V → V) (_∙_ : F → F → F) (_+₁_ : V → V → V) (_+₂_ : F → F → F) (e₁ : V) (e₂ : F) : Set where
  constructor
    prfVecSpace
  field
    isAbelianGroup : IsAbelianGroup _+₁_ e₁
    distF          : (a : F) → (u v : V) → a ∘ (u +₁ v) ≡ (a ∘ u) +₁ (a ∘ v)
    distV          : (a b : F) → (v : V) → (a +₂ b) ∘ v ≡ (a ∘ v) +₁ (b ∘ v)
    compat         : (a b : F) → (v : V) → a ∘ (b ∘ v) ≡ (a ∙ b) ∘ v
    scalid         : ∀ v → e₂ ∘ v ≡ v


record IsMatr {K : Ring} : Set2 where
  constructor
    prfMatr
  field
    hoge : Set1
    
open import Data.List
open import Data.Char

-- regardCategoryAsMonoid : (C : Category) → (a : Category.Object C) → Monoid
-- regardCategoryAsMonoid (makeCat Object Arrow identity composition associativity unit_law_left unit_law_right) a =
--   record {
--     uset = Arrow a a ;
--     e = identity a ;
--     ∘ = composition ;
--     isMonoid = {!!} }

    -- Object : Set
    -- Arrow : Object → Object → Set
    -- identity : (a : Object) → Arrow a a
    -- composition : {a b c : Object} → Arrow a b → Arrow b c → Arrow a c
    -- associativity : {a b c d : Object} → (f : Arrow a b) → (g : Arrow b c) → (h : Arrow c d) →
    --   composition (composition f g) h ≡ composition f (composition g h)
    -- unit_law_left  : {a b : Object} → (f : Arrow a b) → composition f (identity b) ≡ f
    -- unit_law_right : {b c : Object} → (g : Arrow b c) → composition (identity b) g ≡ g

data Unit : Set where
  * : Unit

regardGroupAsCategory : Group → Category
regardGroupAsCategory (makeGroup uset e ∘ (prfGroup (prfMonoid (prfSemigroup assoc) (proj₁ , proj₂)) inverse))
  = makeCat Unit (λ _ _ → uset) (λ _ → e) ∘ assoc proj₂ proj₁

-- p.11
{-
  A Category is discrete when every arrow is an identity. Every Set X is the set of objects of a
  discrete category (just add one identity arrow x → x for each x ∈ X), and every discrete category
  is so determined by its set of objects. Thus, discrete categories are sets.
-}

-- isDiscrete : Category → Set 
-- isDiscrete (makeCat O A id comp asso ul ur) -- (makeCat Object Arrow identity composition associativity unit_law_left unit_law_right)
--  = (a b : O) → (f : A _ b) → f ≡ id b
--   = (a b c x : O) → (idb : A x x) → (f : A a b) → (g : A b c)


data ０Object : Set where -- There is no object.

data ０Arrow : ０Object → ０Object → Set where -- There is no arrow.
    
０ : Category
０ = record
       { Object = ０Object
       ; Arrow = ０Arrow
       ; identity = λ ()
       ; composition = λ {a} {b} {c} _ → λ ()
       ; associativity = λ {a} {b} {c} {d} f g → λ ()
       ; unit_law_left = λ {a} {b} → λ ()
       ; unit_law_right = λ {b} {c} → λ ()
       }

data １Object : Set where
  * : １Object

data １Arrow : １Object → １Object → Set where
  *→* : １Arrow * *

id１ : (a : １Object) → １Arrow a a
id１ * = *→*

comp１ : {a b c : １Object} → １Arrow a b → １Arrow b c → １Arrow a c
comp１ *→* *→* = *→*

asso１ : {a b c d : １Object} (f : １Arrow a b) (g : １Arrow b c) (h : １Arrow c d) → comp１ (comp１ f g) h ≡ comp１ f (comp１ g h)
asso１ *→* *→* *→* = refl

unitLaw１Left : {a b : １Object} (f : １Arrow a b) → comp１ f (id１ b) ≡ f
unitLaw１Left *→* = refl

unitLaw１Right : {b c : １Object} (g : １Arrow b c) → comp１ (id１ b) g ≡ g
unitLaw１Right *→* = refl

１ : Category
１ = record
        { Object = １Object
        ; Arrow  = １Arrow
        ; identity = id１
        ; composition = comp１
        ; associativity = asso１
        ; unit_law_left = unitLaw１Left
        ; unit_law_right = unitLaw１Right
        }

data ２Object : Set where
  * : ２Object
  ⋆ : ２Object

data ２Arrow : ２Object → ２Object → Set where
  *→* : ２Arrow * *
  ⋆→⋆ : ２Arrow ⋆ ⋆
  *→⋆ : ２Arrow * ⋆

id２ : (a : ２Object) → ２Arrow a a
id２ * = *→*
id２ ⋆ = ⋆→⋆

comp２ : {a b c : ２Object} → ２Arrow a b → ２Arrow b c → ２Arrow a c
comp２ *→* *→* = *→*
comp２ *→* *→⋆ = *→⋆
comp２ ⋆→⋆ ⋆→⋆ = ⋆→⋆
comp２ *→⋆ ⋆→⋆ = *→⋆

asso２ : {a b c d : ２Object} (f : ２Arrow a b) (g : ２Arrow b c) (h : ２Arrow c d) → comp２ (comp２ f g) h ≡ comp２ f (comp２ g h)
asso２ *→* *→* *→* = refl
asso２ *→* *→* *→⋆ = refl
asso２ *→* *→⋆ ⋆→⋆ = refl
asso２ ⋆→⋆ ⋆→⋆ ⋆→⋆ = refl
asso２ *→⋆ ⋆→⋆ ⋆→⋆ = refl

unitLaw２Left : {a b : ２Object} (f : ２Arrow a b) → comp２ f (id２ b) ≡ f
unitLaw２Left *→* = refl
unitLaw２Left ⋆→⋆ = refl
unitLaw２Left *→⋆ = refl

unitLaw２Right : {b c : ２Object} (g : ２Arrow b c) → comp２ (id２ b) g ≡ g
unitLaw２Right *→* = refl
unitLaw２Right ⋆→⋆ = refl
unitLaw２Right *→⋆ = refl

２ : Category
２ = record
        { Object = ２Object
        ; Arrow = ２Arrow
        ; identity = id２
        ; composition = comp２
        ; associativity = asso２
        ; unit_law_left = unitLaw２Left
        ; unit_law_right = unitLaw２Right
        }

isDiscrete : Category → Set 
isDiscrete (makeCat O A id comp asso ul ur) = (a : O) → (f : A _ _) →  f ≡ (id a)

-- ２isDiscrete : isDiscrete ２
-- ２isDiscrete a f = {!!}
-- --２isDiscrete = λ a b c idb f g → {!!}

-- data ３Object : Set where
--   * : ３Object
--   ⋆ : ３Object
--   # : ３Object

-- data ３Arrow : ３Object → ３Object → Set where
--   *→* : ３Arrow * *
--   ⋆→⋆ : ３Arrow ⋆ ⋆
--   #→# : ３Arrow # #
--   *→⋆ : ３Arrow * ⋆
--   *→# : ３Arrow * #
--   ⋆→# : ３Arrow ⋆ #

-- id３ : (a : ３Object) → ３Arrow a a
-- id３ * = *→*
-- id３ ⋆ = ⋆→⋆
-- id３ # = #→#

-- comp３ : {a b c : ３Object} → ３Arrow a b → ３Arrow b c → ３Arrow a c
-- comp３ *→* *→* = *→*
-- comp３ *→* *→⋆ = *→⋆
-- comp３ *→* *→# = *→#
-- comp３ ⋆→⋆ ⋆→⋆ = ⋆→⋆
-- comp３ ⋆→⋆ ⋆→# = ⋆→#
-- comp３ #→# #→# = #→#
-- comp３ *→⋆ ⋆→⋆ = *→⋆
-- comp３ *→⋆ ⋆→# = *→#
-- comp３ *→# #→# = *→#
-- comp３ ⋆→# #→# = ⋆→#

-- asso３ : {a b c d : ３Object} (f : ３Arrow a b) (g : ３Arrow b c) (h : ３Arrow c d) → comp３ (comp３ f g) h ≡ comp３ f (comp３ g h)
-- asso３ *→* *→* *→* = refl
-- asso３ *→* *→* *→⋆ = refl
-- asso３ *→* *→* *→# = refl
-- asso３ *→* *→⋆ ⋆→⋆ = refl
-- asso３ *→* *→⋆ ⋆→# = refl
-- asso３ *→* *→# #→# = refl
-- asso３ ⋆→⋆ ⋆→⋆ ⋆→⋆ = refl
-- asso３ ⋆→⋆ ⋆→⋆ ⋆→# = refl
-- asso３ ⋆→⋆ ⋆→# #→# = refl
-- asso３ #→# #→# #→# = refl
-- asso３ *→⋆ ⋆→⋆ ⋆→⋆ = refl
-- asso３ *→⋆ ⋆→⋆ ⋆→# = refl
-- asso３ *→⋆ ⋆→# #→# = refl
-- asso３ *→# #→# #→# = refl
-- asso３ ⋆→# #→# #→# = refl

-- unitLeft３ : {a b : ３Object} (f : ３Arrow a b) → comp３ f (id３ b) ≡ f
-- unitLeft３ *→* = refl
-- unitLeft３ ⋆→⋆ = refl
-- unitLeft３ #→# = refl
-- unitLeft３ *→⋆ = refl
-- unitLeft３ *→# = refl
-- unitLeft３ ⋆→# = refl

-- unitRight３ : {b c : ３Object} (g : ３Arrow b c) → comp３ (id３ b) g ≡ g
-- unitRight３ *→* = refl
-- unitRight３ ⋆→⋆ = refl
-- unitRight３ #→# = refl
-- unitRight３ *→⋆ = refl
-- unitRight３ *→# = refl
-- unitRight３ ⋆→# = refl

-- ３ : Category
-- ３ = record
--           { Object = ３Object
--           ; Arrow = ３Arrow
--           ; identity = id３
--           ; composition = comp３
--           ; associativity = asso３
--           ; unit_law_left = unitLeft３
--           ; unit_law_right = unitRight３
--           }

-- data ↓↓Object : Set where
--   a : ↓↓Object
--   b : ↓↓Object

-- data ↓↓Arrow : ↓↓Object → ↓↓Object → Set where
--   a→a  : ↓↓Arrow a a
--   b→b  : ↓↓Arrow b b 
--   a→₁b : ↓↓Arrow a b
--   a→₂b : ↓↓Arrow a b

-- ↓↓id : (x : ↓↓Object) → ↓↓Arrow x x
-- ↓↓id a = a→a
-- ↓↓id b = b→b

-- ↓↓comp : {x : ↓↓Object} {y : ↓↓Object} {z : ↓↓Object} → ↓↓Arrow x y → ↓↓Arrow y z → ↓↓Arrow x z
-- ↓↓comp a→a a→a = a→a
-- ↓↓comp a→a a→₁b = a→₁b
-- ↓↓comp a→a a→₂b = a→₂b
-- ↓↓comp b→b b→b = b→b
-- ↓↓comp a→₁b b→b = a→₁b
-- ↓↓comp a→₂b b→b = a→₂b

-- ↓↓asso : {x y z w : ↓↓Object} (f : ↓↓Arrow x y) (g : ↓↓Arrow y z) (h : ↓↓Arrow z w) → ↓↓comp (↓↓comp f g) h ≡ ↓↓comp f (↓↓comp g h)
-- ↓↓asso a→a a→a a→a = refl
-- ↓↓asso a→a a→a a→₁b = refl
-- ↓↓asso a→a a→a a→₂b = refl
-- ↓↓asso a→a a→₁b b→b = refl
-- ↓↓asso a→a a→₂b b→b = refl
-- ↓↓asso b→b b→b b→b = refl
-- ↓↓asso a→₁b b→b b→b = refl
-- ↓↓asso a→₂b b→b b→b = refl

-- ↓↓unitLeft : {x y : ↓↓Object} (f : ↓↓Arrow x y) → ↓↓comp f (↓↓id y) ≡ f
-- ↓↓unitLeft a→a = refl
-- ↓↓unitLeft b→b = refl
-- ↓↓unitLeft a→₁b = refl
-- ↓↓unitLeft a→₂b = refl

-- ↓↓unitRight : {y z : ↓↓Object} (g : ↓↓Arrow y z) → ↓↓comp (↓↓id y) g ≡ g
-- ↓↓unitRight a→a = refl
-- ↓↓unitRight b→b = refl
-- ↓↓unitRight a→₁b = refl
-- ↓↓unitRight a→₂b = refl

-- ↓↓ : Category
-- ↓↓ = record
--          { Object = ↓↓Object
--          ; Arrow = ↓↓Arrow
--          ; identity = ↓↓id
--          ; composition = ↓↓comp
--          ; associativity = ↓↓asso
--          ; unit_law_left = ↓↓unitLeft
--          ; unit_law_right = ↓↓unitRight
--          }

-- {--
-- record Functor (C B : Category) : Set1 where
--   private
--     module C = Category C
--     module B = Category B
--   field
--     object-function : C.Object → B.Object
--     arrow-function  : {c c' : C.Object} → C.Arrow c c' → B.Arrow (object-function c) (object-function c')
--     law₁ : {c : C.Object} → arrow-function (C.identity c) ≡ B.identity (object-function c)
--     law₂ : {a b c : C.Object} → {f : C.Arrow a b} → {g : C.Arrow b c}
--               → arrow-function (C.composition f g) ≡ B.composition (arrow-function f) (arrow-function g)
-- --}

-- record Functor (C B : Category) : Set1 where
--   field
--     object-function : Category.Object C → Category.Object B
--     arrow-function  : {c c' : Category.Object C} → Category.Arrow C c c' → Category.Arrow B (object-function c) (object-function c')
--     law₁ : (c : Category.Object C)
--           → arrow-function ((Category.identity C) c) ≡ (Category.identity B) (object-function c)
--      -- p.13 (1) left
--      -- T_{A}(1_{c}) ≡ 1_{T_{O}(C)}
--      -- map an Object in the Category C to its identity Arrow and map that to an Arrow in the Category B
--      -- map an object in the Category C to an Object in the Category B and map that to its identity Arrow.
--     law₂ : {a b c : Category.Object C} → (f : Category.Arrow C a b) → (g : Category.Arrow C b c)
--           → arrow-function (Category.composition C f g) ≡ Category.composition B (arrow-function f) (arrow-function g)
--       -- p.13 (1) right
--       -- T_{A}(g ∘ f) ≡ T_{A}(g) ∘ T_{A}(f)
--       -- compose f with g and map by T_{A} equals to map f and g by T_{A} then compose them


-- １→１ : Functor １ １
-- １→１ = record
--            { object-function = λ x → x ; arrow-function = λ x → x ; law₁ = λ _ → refl ; law₂ = λ _ _ → refl }

-- To : Category.Object ３ → Category.Object ２
-- To * = *
-- To ⋆ = *
-- To # = ⋆

-- Ta : {c c' : Category.Object ３} → Category.Arrow ３ c c' → Category.Arrow ２ (To c) (To c')
-- Ta *→* = *→*
-- Ta ⋆→⋆ = *→*
-- Ta #→# = ⋆→⋆
-- Ta *→⋆ = *→*
-- Ta *→# = *→⋆
-- Ta ⋆→# = *→⋆


-- ３→２law₁ : (c : Category.Object ３) → Ta (Category.identity ３ c) ≡ Category.identity ２ (To c)
-- ３→２law₁ * = refl
-- ３→２law₁ ⋆ = refl
-- ３→２law₁ # = refl

-- ３→２law₂ : {a₁ b₁ c : Category.Object ３} (f : Category.Arrow ３ a₁ b₁) (g : Category.Arrow ３ b₁ c) → Ta (Category.composition ３ f g) ≡ Category.composition ２ (Ta f) (Ta g)
-- ３→２law₂ *→* *→* = refl
-- ３→２law₂ *→* *→⋆ = refl
-- ３→２law₂ *→* *→# = refl
-- ３→２law₂ ⋆→⋆ ⋆→⋆ = refl
-- ３→２law₂ ⋆→⋆ ⋆→# = refl
-- ３→２law₂ #→# #→# = refl
-- ３→２law₂ *→⋆ ⋆→⋆ = refl
-- ３→２law₂ *→⋆ ⋆→# = refl
-- ３→２law₂ *→# #→# = refl
-- ３→２law₂ ⋆→# #→# = refl

-- ３→２ : Functor ３ ２
-- ３→２ = record
--            { object-function = To ; arrow-function = Ta ; law₁ = ３→２law₁ ; law₂ = ３→２law₂ }

-- record Natural-Transformation {C B : Category} (S T : Functor C B) : Set1 where
--   field
--     natural-transformation : (c : Category.Object C) → Category.Arrow B (Functor.object-function S c) (Functor.object-function T c)
--     law : (c c' : Category.Object C) → (f : Category.Arrow C c c')
--       → Category.composition B (natural-transformation c) (Functor.arrow-function T f) ≡ Category.composition B (Functor.arrow-function S f) (natural-transformation c')

-- {--
-- nt３→２ : (c : Category.Object ３) → Category.Arrow ２ (Functor.object-function ３→２ c) (Functor.object-function ３→２ c)
-- nt３→２ * = *→*
-- nt３→２ ⋆ = *→*
-- nt３→２ # = ⋆→⋆      

-- τ３→２ : Natural-Transformation ３→２ ３→２
-- τ３→２ = record { natural-transformation = nt３→２ ; law = {!!} }
-- --}

-- data 磯野家-Object : Set where
--   カツオ : 磯野家-Object
--   サザエ : 磯野家-Object
--   ワカメ : 磯野家-Object

-- data 磯野家-Arrow : 磯野家-Object → 磯野家-Object → Set where
--   ワカメ→ワカメ : 磯野家-Arrow ワカメ ワカメ
--   カツオ→カツオ : 磯野家-Arrow カツオ カツオ
--   サザエ→サザエ : 磯野家-Arrow サザエ サザエ
--   カツオ→ワカメ : 磯野家-Arrow カツオ ワカメ
--   サザエ→ワカメ : 磯野家-Arrow サザエ ワカメ
--   サザエ→カツオ : 磯野家-Arrow サザエ カツオ

-- 磯野id : (x : 磯野家-Object) → 磯野家-Arrow x x
-- 磯野id カツオ = カツオ→カツオ
-- 磯野id サザエ = サザエ→サザエ
-- 磯野id ワカメ = ワカメ→ワカメ

-- 磯野com : {a₁ : 磯野家-Object} {b₁ : 磯野家-Object} → {c₁ : 磯野家-Object} → 磯野家-Arrow a₁ b₁ → 磯野家-Arrow b₁ c₁ → 磯野家-Arrow a₁ c₁
-- 磯野com ワカメ→ワカメ ワカメ→ワカメ = ワカメ→ワカメ
-- 磯野com カツオ→カツオ カツオ→カツオ = カツオ→カツオ
-- 磯野com カツオ→カツオ カツオ→ワカメ = カツオ→ワカメ
-- 磯野com サザエ→サザエ サザエ→サザエ = サザエ→サザエ
-- 磯野com サザエ→サザエ サザエ→ワカメ = サザエ→ワカメ
-- 磯野com サザエ→サザエ サザエ→カツオ = サザエ→カツオ
-- 磯野com カツオ→ワカメ ワカメ→ワカメ = カツオ→ワカメ
-- 磯野com サザエ→ワカメ ワカメ→ワカメ = サザエ→ワカメ
-- 磯野com サザエ→カツオ カツオ→カツオ = サザエ→カツオ
-- 磯野com サザエ→カツオ カツオ→ワカメ = サザエ→ワカメ

-- 磯野asso : {a₁ : 磯野家-Object} {b₁ : 磯野家-Object} {c d : 磯野家-Object} (f : 磯野家-Arrow a₁ b₁) (g : 磯野家-Arrow b₁ c) (h : 磯野家-Arrow c d) → 磯野com (磯野com f g) h ≡ 磯野com f (磯野com g h)
-- 磯野asso ワカメ→ワカメ ワカメ→ワカメ ワカメ→ワカメ = refl
-- 磯野asso カツオ→カツオ カツオ→カツオ カツオ→カツオ = refl
-- 磯野asso カツオ→カツオ カツオ→カツオ カツオ→ワカメ = refl
-- 磯野asso カツオ→カツオ カツオ→ワカメ ワカメ→ワカメ = refl
-- 磯野asso サザエ→サザエ サザエ→サザエ サザエ→サザエ = refl
-- 磯野asso サザエ→サザエ サザエ→サザエ サザエ→ワカメ = refl
-- 磯野asso サザエ→サザエ サザエ→サザエ サザエ→カツオ = refl
-- 磯野asso サザエ→サザエ サザエ→ワカメ ワカメ→ワカメ = refl
-- 磯野asso サザエ→サザエ サザエ→カツオ カツオ→カツオ = refl
-- 磯野asso サザエ→サザエ サザエ→カツオ カツオ→ワカメ = refl
-- 磯野asso カツオ→ワカメ ワカメ→ワカメ ワカメ→ワカメ = refl
-- 磯野asso サザエ→ワカメ ワカメ→ワカメ ワカメ→ワカメ = refl
-- 磯野asso サザエ→カツオ カツオ→カツオ カツオ→カツオ = refl
-- 磯野asso サザエ→カツオ カツオ→カツオ カツオ→ワカメ = refl
-- 磯野asso サザエ→カツオ カツオ→ワカメ ワカメ→ワカメ = refl

-- 磯野ul : {a₁ : 磯野家-Object} {b₁ : 磯野家-Object} (f : 磯野家-Arrow a₁ b₁) → 磯野com f (磯野id b₁) ≡ f
-- 磯野ul ワカメ→ワカメ = refl
-- 磯野ul カツオ→カツオ = refl
-- 磯野ul サザエ→サザエ = refl
-- 磯野ul カツオ→ワカメ = refl
-- 磯野ul サザエ→ワカメ = refl
-- 磯野ul サザエ→カツオ = refl

-- 磯野ur : {b₁ : 磯野家-Object} {c : 磯野家-Object} (g : 磯野家-Arrow b₁ c) → 磯野com (磯野id b₁) g ≡ g
-- 磯野ur ワカメ→ワカメ = refl
-- 磯野ur カツオ→カツオ = refl
-- 磯野ur サザエ→サザエ = refl
-- 磯野ur カツオ→ワカメ = refl
-- 磯野ur サザエ→ワカメ = refl
-- 磯野ur サザエ→カツオ = refl

-- 磯野家 : Category
-- 磯野家 = record
--            { Object = 磯野家-Object
--            ; Arrow = 磯野家-Arrow
--            ; identity = 磯野id
--            ; composition = 磯野com
--            ; associativity = 磯野asso
--            ; unit_law_left = 磯野ul
--            ; unit_law_right = 磯野ur
--            }

-- data カタカナ-Object : Set where
--   エ : カタカナ-Object
--   オ : カタカナ-Object
--   カ : カタカナ-Object
--   サ : カタカナ-Object
--   メ : カタカナ-Object
--   ワ : カタカナ-Object

-- data カタカナ-Arrow : カタカナ-Object → カタカナ-Object → Set where
--   エ→エ : カタカナ-Arrow エ エ
--   オ→オ : カタカナ-Arrow オ オ
--   カ→カ : カタカナ-Arrow カ カ
--   サ→サ : カタカナ-Arrow サ サ
--   メ→メ : カタカナ-Arrow メ メ
--   ワ→ワ : カタカナ-Arrow ワ ワ
--   エ→オ : カタカナ-Arrow エ オ
--   エ→メ : カタカナ-Arrow エ メ
--   オ→メ : カタカナ-Arrow オ メ
-- --  カ→メ : カタカナ-Arrow カ メ
-- --  サ→オ : カタカナ-Arrow サ オ
--   サ→カ : カタカナ-Arrow サ カ
-- --  ワ→エ : カタカナ-Arrow ワ エ　
--   ワ→カ : カタカナ-Arrow ワ カ
--   ワ→サ : カタカナ-Arrow ワ サ


-- カタカナid : (x : カタカナ-Object) → カタカナ-Arrow x x
-- カタカナid カ = カ→カ
-- カタカナid サ = サ→サ
-- カタカナid ワ = ワ→ワ
-- カタカナid オ = オ→オ
-- カタカナid エ = エ→エ
-- カタカナid メ = メ→メ

-- -- カタカナcom : {a₁ : カタカナ-Object} {b₁ : カタカナ-Object} {c : カタカナ-Object} → カタカナ-Arrow a₁ b₁ → カタカナ-Arrow b₁ c → カタカナ-Arrow a₁ c
-- -- カタカナcom e d = {!!}

-- -- カタカナasso : {a₁ : カタカナ-Object} {b₁ : カタカナ-Object} {c d : カタカナ-Object} (f : カタカナ-Arrow a₁ b₁) (g : カタカナ-Arrow b₁ c) (h : カタカナ-Arrow c d) → カタカナcom (カタカナcom f g) h ≡ カタカナcom f (カタカナcom g h)
-- -- カタカナasso エ→エ エ→エ エ→エ = refl
-- -- カタカナasso エ→エ エ→エ エ→オ = refl
-- -- カタカナasso エ→エ エ→エ エ→メ = refl
-- -- カタカナasso エ→エ エ→オ オ→オ = refl
-- -- カタカナasso エ→エ エ→オ オ→メ = refl
-- -- カタカナasso エ→エ エ→メ メ→メ = refl
-- -- カタカナasso オ→オ オ→オ オ→オ = refl
-- -- カタカナasso オ→オ オ→オ オ→メ = refl
-- -- カタカナasso オ→オ オ→メ メ→メ = refl
-- -- カタカナasso カ→カ カ→カ カ→カ = refl
-- -- カタカナasso サ→サ サ→サ サ→サ = refl
-- -- カタカナasso サ→サ サ→サ サ→カ = refl
-- -- カタカナasso サ→サ サ→カ カ→カ = refl
-- -- カタカナasso メ→メ メ→メ メ→メ = refl
-- -- カタカナasso ワ→ワ ワ→ワ ワ→ワ = refl
-- -- カタカナasso ワ→ワ ワ→ワ ワ→カ = refl
-- -- カタカナasso ワ→ワ ワ→ワ ワ→サ = refl
-- -- カタカナasso ワ→ワ ワ→カ カ→カ = refl
-- -- カタカナasso ワ→ワ ワ→サ サ→サ = refl
-- -- カタカナasso ワ→ワ ワ→サ サ→カ = refl
-- -- カタカナasso エ→オ オ→オ オ→オ = refl
-- -- カタカナasso エ→オ オ→オ オ→メ = refl
-- -- カタカナasso エ→オ オ→メ メ→メ = refl
-- -- カタカナasso エ→メ メ→メ メ→メ = refl
-- -- カタカナasso オ→メ メ→メ メ→メ = refl
-- -- カタカナasso サ→カ カ→カ カ→カ = refl
-- -- カタカナasso ワ→カ カ→カ カ→カ = refl
-- -- カタカナasso ワ→サ サ→サ サ→サ = refl
-- -- カタカナasso ワ→サ サ→サ サ→カ = refl
-- -- カタカナasso ワ→サ サ→カ カ→カ = refl      

-- -- カタカナul : {a₁ : カタカナ-Object} {b₁ : カタカナ-Object} (f : カタカナ-Arrow a₁ b₁) → カタカナcom f (カタカナid b₁) ≡ f
-- -- カタカナul エ→エ = refl
-- -- カタカナul オ→オ = refl
-- -- カタカナul カ→カ = refl
-- -- カタカナul サ→サ = refl
-- -- カタカナul メ→メ = refl
-- -- カタカナul ワ→ワ = refl
-- -- カタカナul エ→オ = refl
-- -- カタカナul エ→メ = refl
-- -- カタカナul オ→メ = refl
-- -- カタカナul サ→カ = refl
-- -- カタカナul ワ→カ = refl
-- -- カタカナul ワ→サ = refl

-- -- カタカナur : {b₁ : カタカナ-Object} {c : カタカナ-Object} (g : カタカナ-Arrow b₁ c) → カタカナcom (カタカナid b₁) g ≡ g
-- -- カタカナur エ→エ = refl
-- -- カタカナur オ→オ = refl
-- -- カタカナur カ→カ = refl
-- -- カタカナur サ→サ = refl
-- -- カタカナur メ→メ = refl
-- -- カタカナur ワ→ワ = refl
-- -- カタカナur エ→オ = refl
-- -- カタカナur エ→メ = refl
-- -- カタカナur オ→メ = refl
-- -- カタカナur サ→カ = refl
-- -- カタカナur ワ→カ = refl
-- -- カタカナur ワ→サ = refl

-- -- カタカナ : Category
-- -- カタカナ = record
-- --              { Object = カタカナ-Object
-- --              ; Arrow = カタカナ-Arrow
-- --              ; identity = カタカナid
-- --              ; composition = カタカナcom
-- --              ; associativity = カタカナasso
-- --              ; unit_law_left = カタカナul
-- --              ; unit_law_right = カタカナur
-- --              }

-- -- S磯→カo : Category.Object 磯野家 → Category.Object カタカナ
-- -- S磯→カo カツオ = サ
-- -- S磯→カo サザエ = ワ
-- -- S磯→カo ワカメ = カ

-- -- S磯→カa : {c c' : Category.Object 磯野家} → Category.Arrow 磯野家 c c' → Category.Arrow カタカナ (S磯→カo c) (S磯→カo c')
-- -- S磯→カa ワカメ→ワカメ = カ→カ
-- -- S磯→カa カツオ→カツオ = サ→サ
-- -- S磯→カa サザエ→サザエ = ワ→ワ
-- -- S磯→カa カツオ→ワカメ = サ→カ
-- -- S磯→カa サザエ→ワカメ = ワ→カ
-- -- S磯→カa サザエ→カツオ = ワ→サ

-- -- S磯→カl₁ : (c : Category.Object 磯野家) → S磯→カa (Category.identity 磯野家 c) ≡ Category.identity カタカナ (S磯→カo c)
-- -- S磯→カl₁ カツオ = refl
-- -- S磯→カl₁ サザエ = refl
-- -- S磯→カl₁ ワカメ = refl

-- -- S磯→カl₂ : {a₁ : Category.Object 磯野家} {b₁ : Category.Object 磯野家} {c : Category.Object 磯野家} (f : Category.Arrow 磯野家 a₁ b₁) (g : Category.Arrow 磯野家 b₁ c) → S磯→カa (Category.composition 磯野家 f g) ≡ Category.composition カタカナ (S磯→カa f) (S磯→カa g)
-- -- S磯→カl₂ ワカメ→ワカメ ワカメ→ワカメ = refl
-- -- S磯→カl₂ カツオ→カツオ カツオ→カツオ = refl
-- -- S磯→カl₂ カツオ→カツオ カツオ→ワカメ = refl
-- -- S磯→カl₂ サザエ→サザエ サザエ→サザエ = refl
-- -- S磯→カl₂ サザエ→サザエ サザエ→ワカメ = refl
-- -- S磯→カl₂ サザエ→サザエ サザエ→カツオ = refl
-- -- S磯→カl₂ カツオ→ワカメ ワカメ→ワカメ = refl
-- -- S磯→カl₂ サザエ→ワカメ ワカメ→ワカメ = refl
-- -- S磯→カl₂ サザエ→カツオ カツオ→カツオ = refl
-- -- S磯→カl₂ サザエ→カツオ カツオ→ワカメ = refl

-- -- S磯野家→カタカナ : Functor 磯野家 カタカナ
-- -- S磯野家→カタカナ = record
-- --                       { object-function = S磯→カo ; arrow-function = S磯→カa ; law₁ = S磯→カl₁ ; law₂ = S磯→カl₂ }

-- -- T磯→カo : Category.Object 磯野家 → Category.Object カタカナ
-- -- T磯→カo カツオ = オ
-- -- T磯→カo サザエ = エ
-- -- T磯→カo ワカメ = メ

-- -- T磯→カa : {c c' : Category.Object 磯野家} → Category.Arrow 磯野家 c c' → Category.Arrow カタカナ (T磯→カo c) (T磯→カo c')
-- -- T磯→カa ワカメ→ワカメ = メ→メ
-- -- T磯→カa カツオ→カツオ = オ→オ
-- -- T磯→カa サザエ→サザエ = エ→エ
-- -- T磯→カa カツオ→ワカメ = オ→メ
-- -- T磯→カa サザエ→ワカメ = エ→メ
-- -- T磯→カa サザエ→カツオ = エ→オ

-- -- T磯→カl₁ : (c : Category.Object 磯野家) → T磯→カa (Category.identity 磯野家 c) ≡ Category.identity カタカナ (T磯→カo c)
-- -- T磯→カl₁ カツオ = refl
-- -- T磯→カl₁ サザエ = refl
-- -- T磯→カl₁ ワカメ = refl

-- -- T磯→カl₂ : {a₁ : Category.Object 磯野家} {b₁ : Category.Object 磯野家} {c : Category.Object 磯野家} (f : Category.Arrow 磯野家 a₁ b₁) (g : Category.Arrow 磯野家 b₁ c) → T磯→カa (Category.composition 磯野家 f g) ≡ Category.composition カタカナ (T磯→カa f) (T磯→カa g)
-- -- T磯→カl₂ ワカメ→ワカメ ワカメ→ワカメ = refl
-- -- T磯→カl₂ カツオ→カツオ カツオ→カツオ = refl
-- -- T磯→カl₂ カツオ→カツオ カツオ→ワカメ = refl
-- -- T磯→カl₂ サザエ→サザエ サザエ→サザエ = refl
-- -- T磯→カl₂ サザエ→サザエ サザエ→ワカメ = refl
-- -- T磯→カl₂ サザエ→サザエ サザエ→カツオ = refl
-- -- T磯→カl₂ カツオ→ワカメ ワカメ→ワカメ = refl
-- -- T磯→カl₂ サザエ→ワカメ ワカメ→ワカメ = refl
-- -- T磯→カl₂ サザエ→カツオ カツオ→カツオ = refl
-- -- T磯→カl₂ サザエ→カツオ カツオ→ワカメ = refl

-- -- T磯野家→カタカナ : Functor 磯野家 カタカナ
-- -- T磯野家→カタカナ = record
-- --                       { object-function = T磯→カo ; arrow-function = T磯→カa ; law₁ = T磯→カl₁ ; law₂ = T磯→カl₂ }

-- -- τ磯→カ : (c : Category.Object 磯野家) → Category.Arrow カタカナ (Functor.object-function S磯野家→カタカナ c) (Functor.object-function T磯野家→カタカナ c)
-- -- τ磯→カ カツオ = {!!}
-- -- τ磯→カ サザエ = {!!}
-- -- τ磯→カ ワカメ = {!!}

-- -- τ磯野家→カタカナ : Natural-Transformation S磯野家→カタカナ T磯野家→カタカナ
-- -- τ磯野家→カタカナ = record { natural-transformation = τ磯→カ ; law = {!!} }

-- -- open import Data.List
-- -- open import Data.Char

-- -- data StrO : Set where
-- --   * : StrO

-- -- StrA : StrO → StrO → Set
-- -- StrA * * = List Char

-- -- strid : (x : StrO) → StrA x x
-- -- strid * = []

-- -- strcom : {x : StrO} {y : StrO} {z : StrO} → StrA x y → StrA y z → StrA x z
-- -- strcom {*} {*} {*} f g = f ++ g

-- -- right++ : (ps : List Char) → ps ++ [] ≡ ps
-- -- right++ [] = refl
-- -- -- right++ (p ∷ ps) rewrite right++ ps = refl
-- -- right++ (p ∷ ps) with (ps ++ []) | right++ ps
-- -- right++ (p ∷ .[]) | [] | refl = refl
-- -- right++ (p ∷ .(x ∷ g)) | x ∷ g | refl = refl

-- -- strass : {x y z w : StrO} (f : StrA x y) (g : StrA y z) (h : StrA z w) → strcom (strcom f g) h ≡ strcom f (strcom g h)
-- -- strass {*} {*} {*} {*} [] [] [] = refl
-- -- strass {*} {*} {*} {*} [] [] (x ∷ h) = refl
-- -- strass {*} {*} {*} {*} [] (x ∷ g) [] = refl
-- -- strass {*} {*} {*} {*} [] (x ∷ g) (y ∷ h) = refl
-- -- strass {*} {*} {*} {*} (x ∷ f) [] [] = {!!}
-- -- strass {*} {*} {*} {*} (x ∷ f) [] (y ∷ h) = {!!}
-- -- strass {*} {*} {*} {*} (x ∷ f) (y ∷ g) [] = {!!}
-- -- strass {*} {*} {*} {*} (x ∷ f) (y ∷ g) (z ∷ h) = {!!}


-- -- open import Data.Nat

-- -- strull : {x : StrO} {y : StrO} (f : StrA x y) → strcom f (strid y) ≡ f
-- -- strull {*} {*} f = {!!}

-- -- strulr : {y : StrO} {z : StrO} (g : StrA y z) → strcom (strid y) g ≡ g
-- -- strulr {*} {*} [] = refl
-- -- strulr {*} {*} (x ∷ g) = refl

-- -- Str : Category
-- -- Str = record
-- --         { Object = StrO
-- --         ; Arrow = StrA
-- --         ; identity = strid
-- --         ; composition = strcom
-- --         ; associativity = strass
-- --         ; unit_law_left = strull
-- --         ; unit_law_right = strulr
-- --         }

-- data C4v : Set where
--   c0  : C4v
--   c1 : C4v
--   c2 : C4v
--   c3 : C4v

-- _×_ : C4v → C4v → C4v
-- x × c0 = x
-- c0 × y = y
-- c1 × c1 = c2
-- c1 × c2 = c3
-- c1 × c3 = c0
-- c2 × c1 = c3
-- c2 × c2 = c0
-- c2 × c3 = c1
-- c3 × c1 = c0
-- c3 × c2 = c1
-- c3 × c3 = c2

-- data C4vO : Set where
--   * : C4vO

-- C4vA : C4vO → C4vO → Set
-- C4vA * * = C4v

-- C4vid : (a : C4vO) → C4vA a a
-- C4vid * = c0

-- C4vcom : {a b c : C4vO} → C4vA a b → C4vA b c → C4vA a c
-- C4vcom {*} {*} {*} c0 g = g
-- C4vcom {*} {*} {*} f c0 = f
-- C4vcom {*} {*} {*} c1 c1 = c2
-- C4vcom {*} {*} {*} c1 c2 = c3
-- C4vcom {*} {*} {*} c1 c3 = c0
-- C4vcom {*} {*} {*} c2 c1 = c3
-- C4vcom {*} {*} {*} c2 c2 = c0
-- C4vcom {*} {*} {*} c2 c3 = c1
-- C4vcom {*} {*} {*} c3 c1 = c0
-- C4vcom {*} {*} {*} c3 c2 = c1
-- C4vcom {*} {*} {*} c3 c3 = c2

-- C4vass : {a b c d : C4vO} (f : C4vA a b) (g : C4vA b c) (h : C4vA c d) → C4vcom (C4vcom f g) h ≡ C4vcom f (C4vcom g h)
-- C4vass {*} {*} {*} {*} c0 g h = refl
-- C4vass {*} {*} {*} {*} c1 c0 h = refl
-- C4vass {*} {*} {*} {*} c1 c1 c0 = refl
-- C4vass {*} {*} {*} {*} c1 c1 c1 = refl
-- C4vass {*} {*} {*} {*} c1 c1 c2 = refl
-- C4vass {*} {*} {*} {*} c1 c1 c3 = refl
-- C4vass {*} {*} {*} {*} c1 c2 c0 = refl
-- C4vass {*} {*} {*} {*} c1 c2 c1 = refl
-- C4vass {*} {*} {*} {*} c1 c2 c2 = refl
-- C4vass {*} {*} {*} {*} c1 c2 c3 = refl
-- C4vass {*} {*} {*} {*} c1 c3 c0 = refl
-- C4vass {*} {*} {*} {*} c1 c3 c1 = refl
-- C4vass {*} {*} {*} {*} c1 c3 c2 = refl
-- C4vass {*} {*} {*} {*} c1 c3 c3 = refl
-- C4vass {*} {*} {*} {*} c2 c0 h = refl
-- C4vass {*} {*} {*} {*} c2 c1 c0 = refl
-- C4vass {*} {*} {*} {*} c2 c1 c1 = refl
-- C4vass {*} {*} {*} {*} c2 c1 c2 = refl
-- C4vass {*} {*} {*} {*} c2 c1 c3 = refl
-- C4vass {*} {*} {*} {*} c2 c2 c0 = refl
-- C4vass {*} {*} {*} {*} c2 c2 c1 = refl
-- C4vass {*} {*} {*} {*} c2 c2 c2 = refl
-- C4vass {*} {*} {*} {*} c2 c2 c3 = refl
-- C4vass {*} {*} {*} {*} c2 c3 c0 = refl
-- C4vass {*} {*} {*} {*} c2 c3 c1 = refl
-- C4vass {*} {*} {*} {*} c2 c3 c2 = refl
-- C4vass {*} {*} {*} {*} c2 c3 c3 = refl
-- C4vass {*} {*} {*} {*} c3 c0 h = refl
-- C4vass {*} {*} {*} {*} c3 c1 c0 = refl
-- C4vass {*} {*} {*} {*} c3 c1 c1 = refl
-- C4vass {*} {*} {*} {*} c3 c1 c2 = refl
-- C4vass {*} {*} {*} {*} c3 c1 c3 = refl
-- C4vass {*} {*} {*} {*} c3 c2 c0 = refl
-- C4vass {*} {*} {*} {*} c3 c2 c1 = refl
-- C4vass {*} {*} {*} {*} c3 c2 c2 = refl
-- C4vass {*} {*} {*} {*} c3 c2 c3 = refl
-- C4vass {*} {*} {*} {*} c3 c3 c0 = refl
-- C4vass {*} {*} {*} {*} c3 c3 c1 = refl
-- C4vass {*} {*} {*} {*} c3 c3 c2 = refl
-- C4vass {*} {*} {*} {*} c3 c3 c3 = refl

-- c4vulf : {a b : C4vO} (f : C4vA a b) → C4vcom f (C4vid b) ≡ f
-- c4vulf {*} {*} c0 = refl
-- c4vulf {*} {*} c1 = refl
-- c4vulf {*} {*} c2 = refl
-- c4vulf {*} {*} c3 = refl

-- c4vulr : {b c : C4vO} (g : C4vA b c) → C4vcom (C4vid b) g ≡ g
-- c4vulr {*} {*} c0 = refl
-- c4vulr {*} {*} c1 = refl
-- c4vulr {*} {*} c2 = refl
-- c4vulr {*} {*} c3 = refl

-- C4vC : Category
-- C4vC = record
--          { Object = C4vO
--          ; Arrow = C4vA
--          ; identity = C4vid
--          ; composition = C4vcom
--          ; associativity = C4vass
--          ; unit_law_left = c4vulf
--          ; unit_law_right = c4vulr
--          }

-- open import Agda.Primitive
-- open import Algebra
-- --open import Algebra.Properties.Group

-- hoge : Group lzero lzero
-- hoge = record
--          { Carrier = {!!} ; _≈_ = {!!} ; _∙_ = {!!} ; ε = {!!} ; _⁻¹ = {!!} ; isGroup = {!!} }

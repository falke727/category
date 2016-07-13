module Category where

open import Relation.Binary.PropositionalEquality

record Category : Set1 where
  field
    Object : Set
    Arrow : Object → Object → Set
    identity : (a : Object) → Arrow a a
    composition : {a b c : Object} → Arrow a b → Arrow b c → Arrow a c
    associativity : {a b c d : Object} → (f : Arrow a b) → (g : Arrow b c) → (h : Arrow c d) →
      composition (composition f g) h ≡ composition f (composition g h)
    unit_law_left  : {a b : Object} → (f : Arrow a b) → composition f (identity b) ≡ f
    unit_law_right : {b c : Object} → (g : Arrow b c) → composition (identity b) g ≡ g

data ０ : Set where -- There is no object.

data ０Arrow : ０ → ０ → Set where -- There is no arrow.
    
０IsCategory : Category
０IsCategory = record
                   { Object = ０
                   ; Arrow = ０Arrow
                   ; identity = λ ()
                   ; composition = λ {a} {b} {c} _ → λ ()
                   ; associativity = λ {a} {b} {c} {d} f g → λ ()
                   ; unit_law_left = λ {a} {b} → λ ()
                   ; unit_law_right = λ {b} {c} → λ ()
                   }

data １ : Set where
  * : １

data １Arrow : １ → １ → Set where
  *→* : １Arrow * *

id１ : (a : １) → １Arrow a a
id１ * = *→*

comp１ : {a b c : １} → １Arrow a b → １Arrow b c → １Arrow a c
comp１ *→* *→* = *→*

asso１ : {a b c d : １} (f : １Arrow a b) (g : １Arrow b c) (h : １Arrow c d) → comp１ (comp１ f g) h ≡ comp１ f (comp１ g h)
asso１ *→* *→* *→* = refl

unitLaw１Left : {a b : １} (f : １Arrow a b) → comp１ f (id１ b) ≡ f
unitLaw１Left *→* = refl

unitLaw１Right : {b c : １} (g : １Arrow b c) → comp１ (id１ b) g ≡ g
unitLaw１Right *→* = refl

１IsCategory : Category
１IsCategory = record
                  { Object = １
                  ; Arrow  = １Arrow
                  ; identity = id１
                  ; composition = comp１
                  ; associativity = asso１
                  ; unit_law_left = unitLaw１Left
                  ; unit_law_right = unitLaw１Right
                  }

data ２ : Set where
  * : ２
  ⋆ : ２

data ２Arrow : ２ → ２ → Set where
  *→* : ２Arrow * *
  ⋆→⋆ : ２Arrow ⋆ ⋆
  *→⋆ : ２Arrow * ⋆

id２ : (a : ２) → ２Arrow a a
id２ * = *→*
id２ ⋆ = ⋆→⋆

comp２ : {a b c : ２} → ２Arrow a b → ２Arrow b c → ２Arrow a c
comp２ *→* *→* = *→*
comp２ *→* *→⋆ = *→⋆
comp２ ⋆→⋆ ⋆→⋆ = ⋆→⋆
comp２ *→⋆ ⋆→⋆ = *→⋆

asso２ : {a b c d : ２} (f : ２Arrow a b) (g : ２Arrow b c) (h : ２Arrow c d) → comp２ (comp２ f g) h ≡ comp２ f (comp２ g h)
asso２ *→* *→* *→* = refl
asso２ *→* *→* *→⋆ = refl
asso２ *→* *→⋆ ⋆→⋆ = refl
asso２ ⋆→⋆ ⋆→⋆ ⋆→⋆ = refl
asso２ *→⋆ ⋆→⋆ ⋆→⋆ = refl

unitLaw２Left : {a b : ２} (f : ２Arrow a b) → comp２ f (id２ b) ≡ f
unitLaw２Left *→* = refl
unitLaw２Left ⋆→⋆ = refl
unitLaw２Left *→⋆ = refl

unitLaw２Right : {b c : ２} (g : ２Arrow b c) → comp２ (id２ b) g ≡ g
unitLaw２Right *→* = refl
unitLaw２Right ⋆→⋆ = refl
unitLaw２Right *→⋆ = refl

２IsCategory : Category
２IsCategory = record
                  { Object = ２
                  ; Arrow = ２Arrow
                  ; identity = id２
                  ; composition = comp２
                  ; associativity = asso２
                  ; unit_law_left = unitLaw２Left
                  ; unit_law_right = unitLaw２Right
                  }

data ３ : Set where
  * : ３
  ⋆ : ３
  # : ３

data ３Arrow : ３ → ３ → Set where
  *→* : ３Arrow * *
  ⋆→⋆ : ３Arrow ⋆ ⋆
  #→# : ３Arrow # #
  *→⋆ : ３Arrow * ⋆
  *→# : ３Arrow * #
  ⋆→# : ３Arrow ⋆ #

id３ : (a : ３) → ３Arrow a a
id３ * = *→*
id３ ⋆ = ⋆→⋆
id３ # = #→#

comp３ : {a b c : ３} → ３Arrow a b → ３Arrow b c → ３Arrow a c
comp３ *→* *→* = *→*
comp３ *→* *→⋆ = *→⋆
comp３ *→* *→# = *→#
comp３ ⋆→⋆ ⋆→⋆ = ⋆→⋆
comp３ ⋆→⋆ ⋆→# = ⋆→#
comp３ #→# #→# = #→#
comp３ *→⋆ ⋆→⋆ = *→⋆
comp３ *→⋆ ⋆→# = *→#
comp３ *→# #→# = *→#
comp３ ⋆→# #→# = ⋆→#

asso３ : {a b c d : ３} (f : ３Arrow a b) (g : ３Arrow b c) (h : ３Arrow c d) → comp３ (comp３ f g) h ≡ comp３ f (comp３ g h)
asso３ *→* *→* *→* = refl
asso３ *→* *→* *→⋆ = refl
asso３ *→* *→* *→# = refl
asso３ *→* *→⋆ ⋆→⋆ = refl
asso３ *→* *→⋆ ⋆→# = refl
asso３ *→* *→# #→# = refl
asso３ ⋆→⋆ ⋆→⋆ ⋆→⋆ = refl
asso３ ⋆→⋆ ⋆→⋆ ⋆→# = refl
asso３ ⋆→⋆ ⋆→# #→# = refl
asso３ #→# #→# #→# = refl
asso３ *→⋆ ⋆→⋆ ⋆→⋆ = refl
asso３ *→⋆ ⋆→⋆ ⋆→# = refl
asso３ *→⋆ ⋆→# #→# = refl
asso３ *→# #→# #→# = refl
asso３ ⋆→# #→# #→# = refl

unitLeft３ : {a b : ３} (f : ３Arrow a b) → comp３ f (id３ b) ≡ f
unitLeft３ *→* = refl
unitLeft３ ⋆→⋆ = refl
unitLeft３ #→# = refl
unitLeft３ *→⋆ = refl
unitLeft３ *→# = refl
unitLeft３ ⋆→# = refl

unitRight３ : {b c : ３} (g : ３Arrow b c) → comp３ (id３ b) g ≡ g
unitRight３ *→* = refl
unitRight３ ⋆→⋆ = refl
unitRight３ #→# = refl
unitRight３ *→⋆ = refl
unitRight３ *→# = refl
unitRight３ ⋆→# = refl

３IsCategory : Category
３IsCategory = record
                    { Object = ３
                    ; Arrow = ３Arrow
                    ; identity = id３
                    ; composition = comp３
                    ; associativity = asso３
                    ; unit_law_left = unitLeft３
                    ; unit_law_right = unitRight３
                    }

data ↓↓ : Set where
  a : ↓↓
  b : ↓↓

data ↓↓Arrow : ↓↓ → ↓↓ → Set where
  a→a  : ↓↓Arrow a a
  b→b  : ↓↓Arrow b b 
  a→₁b : ↓↓Arrow a b
  a→₂b : ↓↓Arrow a b

↓↓id : (x : ↓↓) → ↓↓Arrow x x
↓↓id a = a→a
↓↓id b = b→b

↓↓comp : {x : ↓↓} {y : ↓↓} {z : ↓↓} → ↓↓Arrow x y → ↓↓Arrow y z → ↓↓Arrow x z
↓↓comp a→a a→a = a→a
↓↓comp a→a a→₁b = a→₁b
↓↓comp a→a a→₂b = a→₂b
↓↓comp b→b b→b = b→b
↓↓comp a→₁b b→b = a→₁b
↓↓comp a→₂b b→b = a→₂b

↓↓asso : {x : ↓↓} {y : ↓↓} {z w : ↓↓} (f : ↓↓Arrow x y) (g : ↓↓Arrow y z) (h : ↓↓Arrow z w) → ↓↓comp (↓↓comp f g) h ≡ ↓↓comp f (↓↓comp g h)
↓↓asso a→a a→a a→a = refl
↓↓asso a→a a→a a→₁b = refl
↓↓asso a→a a→a a→₂b = refl
↓↓asso a→a a→₁b b→b = refl
↓↓asso a→a a→₂b b→b = refl
↓↓asso b→b b→b b→b = refl
↓↓asso a→₁b b→b b→b = refl
↓↓asso a→₂b b→b b→b = refl

↓↓unitLeft : {x : ↓↓} {y : ↓↓} (f : ↓↓Arrow x y) → ↓↓comp f (↓↓id y) ≡ f
↓↓unitLeft a→a = refl
↓↓unitLeft b→b = refl
↓↓unitLeft a→₁b = refl
↓↓unitLeft a→₂b = refl

↓↓unitRight : {y : ↓↓} {z : ↓↓} (g : ↓↓Arrow y z) → ↓↓comp (↓↓id y) g ≡ g
↓↓unitRight a→a = refl
↓↓unitRight b→b = refl
↓↓unitRight a→₁b = refl
↓↓unitRight a→₂b = refl

↓↓IsCategory : Category
↓↓IsCategory = record
                   { Object = ↓↓
                   ; Arrow = ↓↓Arrow
                   ; identity = ↓↓id
                   ; composition = ↓↓comp
                   ; associativity = ↓↓asso
                   ; unit_law_left = ↓↓unitLeft
                   ; unit_law_right = ↓↓unitRight
                   }

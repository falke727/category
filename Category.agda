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

data Zero : Set where -- There is no object.

data ZeroArrow : Zero → Zero → Set where -- There is no arrow.
    
ZeroIsCategory : Category
ZeroIsCategory = record
                   { Object = Zero
                   ; Arrow = λ _ → λ ()
                   ; identity = λ ()
                   ; composition = λ {a} {b} → λ {}
                   ; associativity = λ {a} {b} {c} → λ {}
                   ; unit_law_left = λ {a} → λ {}
                   ; unit_law_right = λ {b} → λ {}
                   }

data One : Set where
  * : One

data OneArrow : One → One → Set where
  *→* : OneArrow * *

idOne : (a : One) → OneArrow a a
idOne * = *→*

compOne : {a b c : One} → OneArrow a b → OneArrow b c → OneArrow a c
compOne *→* *→* = *→*

assoOne : {a b c d : One} (f : OneArrow a b) (g : OneArrow b c) (h : OneArrow c d) → compOne (compOne f g) h ≡ compOne f (compOne g h)
assoOne *→* *→* *→* = refl

unitLawOneLeft : {a b : One} (f : OneArrow a b) → compOne f (idOne b) ≡ f
unitLawOneLeft *→* = refl

unitLawOneRight : {b c : One} (g : OneArrow b c) → compOne (idOne b) g ≡ g
unitLawOneRight *→* = refl

OneIsCategory : Category
OneIsCategory = record
                  { Object = One
                  ; Arrow  = OneArrow
                  ; identity = idOne
                  ; composition = compOne
                  ; associativity = assoOne
                  ; unit_law_left = unitLawOneLeft
                  ; unit_law_right = unitLawOneRight
                  }

data Two : Set where
  * : Two
  ⋆ : Two

data TwoArrow : Two → Two → Set where
  *→* : TwoArrow * *
  ⋆→⋆ : TwoArrow ⋆ ⋆
  *→⋆ : TwoArrow * ⋆

idTwo : (a : Two) → TwoArrow a a
idTwo * = *→*
idTwo ⋆ = ⋆→⋆

compTwo : {a b c : Two} → TwoArrow a b → TwoArrow b c → TwoArrow a c
compTwo *→* *→* = *→*
compTwo *→* *→⋆ = *→⋆
compTwo ⋆→⋆ ⋆→⋆ = ⋆→⋆
compTwo *→⋆ ⋆→⋆ = *→⋆

assoTwo : {a b c d : Two} (f : TwoArrow a b) (g : TwoArrow b c) (h : TwoArrow c d) → compTwo (compTwo f g) h ≡ compTwo f (compTwo g h)
assoTwo *→* *→* *→* = refl
assoTwo *→* *→* *→⋆ = refl
assoTwo *→* *→⋆ ⋆→⋆ = refl
assoTwo ⋆→⋆ ⋆→⋆ ⋆→⋆ = refl
assoTwo *→⋆ ⋆→⋆ ⋆→⋆ = refl

unitLawTwoLeft : {a b : Two} (f : TwoArrow a b) → compTwo f (idTwo b) ≡ f
unitLawTwoLeft *→* = refl
unitLawTwoLeft ⋆→⋆ = refl
unitLawTwoLeft *→⋆ = refl

unitLawTwoRight : {b c : Two} (g : TwoArrow b c) → compTwo (idTwo b) g ≡ g
unitLawTwoRight *→* = refl
unitLawTwoRight ⋆→⋆ = refl
unitLawTwoRight *→⋆ = refl

TwoIsCategory : Category
TwoIsCategory = record
                  { Object = Two
                  ; Arrow = TwoArrow
                  ; identity = idTwo
                  ; composition = compTwo
                  ; associativity = assoTwo
                  ; unit_law_left = unitLawTwoLeft
                  ; unit_law_right = unitLawTwoRight
                  }

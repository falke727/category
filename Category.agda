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
   
data One : Set where
  * : One

data OneArrow : One → One → Set where
  one-arrow : (x : One) → (y : One) → OneArrow x y

comp : {a b c : One} → OneArrow a b → OneArrow b c → OneArrow a c
comp (one-arrow a b) (one-arrow .b c) = one-arrow a c

one-asso : {a b c d : One} (f : OneArrow a b) (g : OneArrow b c) (h : OneArrow c d) → comp (comp f g) h ≡ comp f (comp g h)
one-asso (one-arrow a b) (one-arrow .b c) (one-arrow .c d) = refl

one-unit-law-left : {a b : One} (f : OneArrow a b) → comp f (one-arrow b b) ≡ f
one-unit-law-left (one-arrow a b) = refl

one-unit-law-right : {b c : One} (g : OneArrow b c) → comp (one-arrow b b) g ≡ g
one-unit-law-right (one-arrow b c) = refl

OneIsCategory : Category
OneIsCategory = record
                  { Object = One
                  ; Arrow  = OneArrow
                  ; identity = λ a → one-arrow a a
                  ; composition = comp
                  ; associativity = one-asso
                  ; unit_law_left = one-unit-law-left
                  ; unit_law_right = one-unit-law-right
                  }

data Zero : Set where

data ZeroArrow : Zero → Zero → Set where
  --zero-arrow : (x : Zero) → (y : Zero) → ZeroArrow {!!} {!!}
  
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

data Two : Set where
  * : Two
  ⋆ : Two

data TwoArrow : Two → Two → Set where
  two-arrow : (x : Two) → (y : Two) → TwoArrow x y

two-comp : {a b c : Two} → TwoArrow a b → TwoArrow b c → TwoArrow a c
two-comp (two-arrow a b) (two-arrow .b c) = two-arrow a c

two-asso : {a b c d : Two} (f : TwoArrow a b) (g : TwoArrow b c) (h : TwoArrow c d) → two-comp (two-comp f g) h ≡ two-comp f (two-comp g h)
two-asso (two-arrow a b) (two-arrow .b c) (two-arrow .c d) = refl

two-unit-law-left : {a b : Two} (f : TwoArrow a b) → two-comp f (two-arrow b b) ≡ f
two-unit-law-left (two-arrow a b) = refl

two-unit-law-right : {b c : Two} (g : TwoArrow b c) → two-comp (two-arrow b b) g ≡ g
two-unit-law-right (two-arrow b c) = refl

TwoIsCategory : Category
TwoIsCategory = record
                  { Object = Two
                  ; Arrow = TwoArrow
                  ; identity = λ a → two-arrow a a
                  ; composition = two-comp
                  ; associativity = two-asso
                  ; unit_law_left = two-unit-law-left
                  ; unit_law_right = two-unit-law-right
                  }

{- using this form

   λ { x → _ ; y → _ }

   we can use case split lambda.
-}

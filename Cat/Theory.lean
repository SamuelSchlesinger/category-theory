/-
Copyright (c) 2026 Samuel G. Schlesinger. All rights reserved.
Authors: Samuel G. Schlesinger
-/
namespace Cat.Theory

/-!

# Category Theory

This file is a self-contained implementation of category theory implemented for
my own education, and perhaps of some readers though that is much less obvious.

A category is a natural mathematical object originally penned by Saunders and
Mac Lane in their 1945 paper "General Theory of Natural Equivalences". At a
birds-eye view, a category is anything with a transitive, reflexive law of
composition. This might sound like a monoid, and it should, but it provides an
extra layer of precision (or "type-safety" by another framing) enabling the
category to not permit every element to compose.

NB: This file was written by hand, without the help of AI. No contributions
will be accepted, it is a personal project.

-/

/--

  A category consists of a set of objects, a set of morphisms parameterized by
  those objects, a law of composition which tells you how to compose those
  morphisms, and, for every object, an identity morphism associated with that
  object.

  There are two laws:
  - associativity: the composition law must not depend on the nesting of
    composition, though order indeed does matter.
  - identity: the identity morphism must be the identity under composition.

  In category theory, we often express things in the form of diagrams. One way
  of viewing this definition as the following, so-called commutative diagram.

              f
          x -----> y
           \       |
            \      |
             \     | g
  compose f g \    |
               \   v
                >  z

  What we mean when we say a diagram is commutative is that, whichever order you
  take through the diagram, the resulting composition is the same.

  The identity diagram is harder to draw in ASCII because it has a loop, but you
  hopefully get the idea. Either way, read through the mathematical definitions
  to understand better.

-/
@[ext]
structure Category where
  obj : Type u
  hom : obj → obj → Type v
  compose : hom x y → hom y z → hom x z
  id : hom x x
  associativity :
    ∀ (f : hom α β) (g : hom β χ) (h : hom χ δ),
      compose f (compose g h) = compose (compose f g) h
  identity :
    compose f id = f ∧ compose id f = f

/--

  The opposite category is simply a flipping of the convention from left to
  right composition.
  
-/
@[simp]
def Category.op (c : Category) : Category where
  obj := c.obj
  hom x y := c.hom y x
  compose f g := c.compose g f
  id := c.id
  associativity := by
    intros f g h
    simp [c.associativity]
  identity := by
    intros a b f
    constructor
    . rw [c.identity.2]
    . rw [c.identity.1]

/-- 

  A morphism is said to be an isomorphism if it has a complementary morphism
  such that composing them together (in either order) results in the identity
  morphism.

-/
@[ext]
structure Category.IsIsomorphism { c : Category } { x y : c.obj } (forward : c.hom x y) where
  backward : c.hom y x
  is_inverse : c.compose forward backward = c.id ∧ c.compose backward forward = c.id

@[simp]
def Category.IsIsomorphism.compose { c : Category } { x y z : c.obj } { f : c.hom x y } { g : c.hom y z }
  (iso₀ : IsIsomorphism f) (iso₁ : IsIsomorphism g) : IsIsomorphism (c.compose f g) := {
    backward := c.compose iso₁.backward iso₀.backward
    is_inverse := by
      constructor
      . rw [← c.associativity f g (c.compose iso₁.backward iso₀.backward)]
        rw [c.associativity g iso₁.backward iso₀.backward]
        rw [iso₁.is_inverse.1]
        simp [c.identity]
        rw [iso₀.is_inverse.1]
      . simp [c.associativity]
        rw [← c.associativity iso₁.backward iso₀.backward f]
        rw [iso₀.is_inverse.2]
        simp [c.identity]
        rw [iso₁.is_inverse.2]
  }

/--

  IsIsomorphisms can be flipped and, because the laws are symmetric, are still
  isomorphisms.

-/
def Category.IsIsomorphism.sym { c : Category } { x y : c.obj } { f : c.hom x y }
  (iso₀ : IsIsomorphism f) : IsIsomorphism iso₀.backward := {
    backward := f
    is_inverse := by
      constructor
      . exact iso₀.is_inverse.2
      . exact iso₀.is_inverse.1
  }

/--

  A wrapper around an IsIsomorphism which hides the specific morphism.

-/
@[ext]
structure Category.Isomorphism { c : Category } (x y : c.obj) where
  forward : c.hom x y
  iso : IsIsomorphism forward

def Category.Isomorphism.sym { c : Category } { x y : c.obj } (iso : Isomorphism x y) : Isomorphism y x :=
  { forward := iso.iso.backward
    iso := iso.iso.sym
  }

@[simp]
def Category.Isomorphism.id { c : Category } { x : c.obj } : Isomorphism x x where
  forward := c.id
  iso := {
    backward := c.id
    is_inverse := c.identity
  }

/--

  The subcategory of all isomorphisms within the given category.

-/
@[simp]
def Category.iso (c : Category) : Category where
  obj := c.obj
  hom x y := Isomorphism x y
  compose f g := {
    forward := c.compose f.forward g.forward
    iso := f.iso.compose g.iso
  }
  id := Isomorphism.id
  associativity := by
    intros α β χ δ f g h
    simp
    constructor
    . simp [ c.associativity ]
    . grind [ c.associativity ]

  identity := by
    intros x y f
    simp
    constructor
    . congr 1
      . simp [ c.identity ]
      . congr 1
        . simp [ c.identity ]
        . simp [ c.identity ]
        . grind
    . congr 1
      . simp [ c.identity ]
      . congr 1
        . simp [ c.identity ] 
        . simp [ c.identity ]
        . grind

/--

  The inverses witnessing isomorphisms are unique.

-/
theorem Category.IsIsomorphism.unique { c : Category } { x y : c.obj }
  (f : c.hom x y) (iso₀ : IsIsomorphism f) (iso₁ : IsIsomorphism f) :
    iso₀.backward = iso₁.backward := by
      calc
        iso₀.backward = c.compose c.id iso₀.backward := by
          simp [c.identity.2]
        _  = c.compose (c.compose iso₁.backward f) iso₀.backward := by
          have h0 := iso₁.is_inverse.2
          rw [h0]
        _  = c.compose iso₁.backward (c.compose f iso₀.backward) := by
          rw [c.associativity]
        _  = c.compose iso₁.backward c.id := by
          have h0 := iso₀.is_inverse.1
          rw [h0]
        _  = iso₁.backward := c.identity.1

/--

  A groupoid is a category for which all morphisms are isomorphisms.

-/
structure Groupoid (c : Category) where
  iso : ∀ (f : c.hom x y), Category.IsIsomorphism f

/--

  The subgroupoid contained within any category defined by all of its isomorphisms.

  In the case where no non-identity morphisms are isomorphisms, this groupoid is
  isomorphic to the discrete groupoid.

-/
@[simp]
def Category.Isomorphism.groupoid (c : Category) : Groupoid (Category.iso c) where
  iso f := {
    backward := f.sym
    is_inverse := by
      constructor
      . simp
        constructor
        . unfold sym
          simp
          rw [f.iso.is_inverse.1]
        . congr 1
          . unfold sym
            simp
            rw [f.iso.is_inverse.1]
          . unfold sym
            simp
            rw [f.iso.sym.is_inverse.2]
          . grind
      . simp
        constructor
        . unfold sym
          simp
          rw [f.iso.is_inverse.2]
        . unfold sym
          simp
          congr 1
          . rw [f.iso.is_inverse.2]
          . rw [f.iso.sym.is_inverse.1]
          . grind
  }

/--


  The equality relation as a type.

-/
inductive Discrete { α : Type } : α → α → Type where
  | deq : Discrete x x

/-- 

  The discrete category only has identity morphisms.

  It is essentially the equality relation.

-/
@[simp]
def Category.discrete (α : Type) [DecidableEq α] : Category where
  obj := α
  hom x y := Discrete x y
  compose {x y z } f g := match f, g with
  | .deq, .deq => .deq
  id := .deq
  associativity := by
    intros α β χ δ f g h
    cases f
    cases g
    cases h
    rfl
  identity := by
    intros x y f
    constructor
    . cases f <;> rfl
    . cases f <;> rfl

/--

  The discrete category is also a groupoid, as it only has identity
  morphisms.

-/
@[simp]
def Groupoid.discrete (α : Type) [DecidableEq α] : Groupoid (Category.discrete α) where
  iso f := {
    backward := by
      cases f
      exact .deq
    is_inverse := by
      cases f
      constructor
      . simp
      . simp
  }

/--

  Our first real category. Here, objects are types and morphisms are functions
  between those types.

-/
@[simp]
def Category.set : Category where
  obj := Type
  hom x y := x → y
  compose f g := g ∘ f
  id x := x
  associativity := by
    intros q w e r t f g
    rfl
  identity := by
    intros a b f
    constructor
    . rfl
    . rfl

/--

  The product of an arbitrary set of categories, indexed by a type α, is also a
  category. Objects are products of objects, morphisms are products of
  morphisms. Composition is parallel composition, identity is parallel
  identity.

-/
@[simp]
def Category.gen_product { α : Type u } (categories : α → Category) : Category where
  obj := (i : α) → (categories i).obj
  hom x y := (i : α) → (categories i).hom (x i) (y i)
  compose f g := λ (i : α) ↦ (categories i).compose (f i) (g i)
  id := λ i ↦ (categories i).id
  associativity := by
    intros α β χ δ f g h
    simp
    funext i
    rw [(categories i).associativity]
  identity := by
    intros x y f
    constructor
    . funext i
      rw [(categories i).identity.1]
    . funext i
      rw [(categories i).identity.2]

/--

  A specialized version of the product category.

  Can be seen to be isomorphic to the gen_product with |α| = 2.

-/
@[simp]
def Category.product (c : Category) (d : Category) : Category where
  obj := c.obj × d.obj
  hom x y := c.hom x.1 y.1 × d.hom x.2 y.2
  compose f g := (c.compose f.1 g.1, d.compose f.2 g.2)
  id := (c.id, d.id)
  associativity := by
    intros α β χ δ f g h
    simp
    rw [d.associativity, c.associativity]
    constructor
    . rfl
    . rfl
  identity := by
    intros x y f
    constructor
    . rw [c.identity.1, d.identity.1]
    . rw [c.identity.2, d.identity.2]

/--

  A functor is a structure preserving map between categories. It contains a way
  to map objects to objects and arrows to arrows.

  It has two laws:
  - homomorphic: the arrow map must preserve composition.
  - identity: the arrow map must preserve identities.

-/
@[ext]
structure Functor (c : Category) (d : Category) where
  obj : c.obj → d.obj
  arr : c.hom x y → d.hom (obj x) (obj y)
  homomorphic :
    ∀ (r : c.hom x y) (t : c.hom y z),
      arr (c.compose r t) = d.compose (arr r) (arr t)
  identity :
    ∀ (x : c.obj),
      arr (c.id (x := x)) = d.id (x := obj x)

/--

  The identity functor simply maps objects to themselves and arrows to
  themselves. Of course this preserves structure

-/
@[simp]
def Functor.id (c : Category) : Functor c c where
  obj x := x
  arr c := c
  homomorphic := by
    intros x y z r t
    rfl
  identity := by
    intros x
    rfl

/--

  The category of categories. Our second category, here the objects are
  categories and morphisms are functors between categories.

-/
@[simp]
def Category.cat : Category where
  obj := Category
  hom := Functor
  compose f g := {
    obj := g.obj ∘ f.obj
    arr := g.arr ∘ f.arr
    homomorphic := by
      intros x y z r t
      simp
      rw [f.homomorphic, g.homomorphic]
    identity := by
      intros x
      simp
      rw [f.identity, g.identity]
  }
  id := @Functor.id
  associativity := by
    intros α β χ δ f g h
    ext
    simp
    simp
    funext x y
    rfl
  identity := by
    intros x x1 f
    constructor
    . ext
      . simp
      . simp
        funext x1 x2
        rfl
    . ext
      . simp
      . simp
        rfl

/--

  The hom functor is a functor from C^op × C to Set. It maps pairs of objects
  to the hom set of C. It maps pairs of arrows to a function which performs
  simultaneous pre- and post-composition. In my head-canon thus, this is the
  sandwich functor.

-/
def Functor.hom (c : Category) : Functor (c.op.product c) Category.set where
  obj x := c.hom x.1 x.2
  arr f := λ g ↦ c.compose (c.compose f.1 g) f.2
  homomorphic := by
    intros x y z r t
    simp
    ext
    simp [← c.associativity]
  identity := by
    intros x
    funext g
    simp
    simp [c.identity]

/--

  A monad for a functor f contains essentially the equipment for composing
  arrows a → f b with arrows b → f c such that the resulting composition
  law forms a category, the Kleisli category. As such, it must also contain
  the identity in that category.

  In functional programming languages, these make a particularly appealing
  abstraction for certain types of control flow, and so many of us are familiar
  with them.

-/
structure Monad (f : Functor c c) where
  bind : c.hom a (f.obj b) → c.hom (f.obj a) (f.obj b)
  pure : c.hom a (f.obj a)
  left_unit : bind pure = c.id (x := f.obj x)
  right_unit : ∀ (h : c.hom a (f.obj b)),
    c.compose pure (bind h) = h
  associativity :
    ∀ (s : c.hom α (f.obj β)) (t : c.hom β (f.obj χ)),
      c.compose (bind s) (bind t) = bind (c.compose s (bind t))

/--

  The identity functor is a monad in a rather uninteresting way.

-/
def Monad.id : Monad (Functor.id c) where
  bind := λ x ↦ x
  pure := c.id
  left_unit := rfl
  right_unit := by
    intros
    simp [c.identity.2]
  associativity := by
    intros α β χ s t
    rfl

/--

  Every monad defines a category via Kleisli composition. Monads are basically
  defined such that this category exists, as we discussed before, and this
  category is what makes monads composable.

-/
@[simp]
def Category.kleisli (m : Functor c c) (monad : Monad m) : Category where
  obj := c.obj
  hom x y := c.hom x (m.obj y)
  compose f g := c.compose f (monad.bind g)
  id := monad.pure
  associativity := by
    intros α β χ δ f g h
    rw [← c.associativity, monad.associativity]
  identity := by
    intros x y f
    constructor
    . rw [monad.left_unit, c.identity.1]
    . rw [monad.right_unit]

/--

  Comonads are the co-thing to a monad. In functional programming, these make
  an appearance, but less so.

-/
structure Comonad (f : Functor c c) where
  extend : c.hom (f.obj a) b → c.hom (f.obj a) (f.obj b)
  extract : c.hom (f.obj a) a
  left_unit : extend extract = c.id (x := f.obj x)
  right_unit : ∀ (h : c.hom (f.obj a) b),
    c.compose (extend h) extract = h
  associativity :
    ∀ (s : c.hom (f.obj α) β) (t : c.hom (f.obj β) χ),
      c.compose (extend s) (extend t) = extend (c.compose (extend s) t)

/--

  The identity functor, again, is a comonad.

-/
def Comonad.id : Comonad (Functor.id c) where
  extend := λ x ↦ x
  extract := c.id
  left_unit := rfl
  right_unit := by
    intros
    simp [c.identity.1]
  associativity := by
    intros α β χ s t
    rfl

/--

  And you wouldn't believe it, there is a category here too.

-/
@[simp]
def Category.cokleisli (w : Functor c c) (comonad : Comonad w) : Category where
  obj := c.obj
  hom x y := c.hom (w.obj x) y 
  compose f g := c.compose (comonad.extend f) g
  id := comonad.extract
  associativity := by
    intros α β χ δ f g h
    rw [c.associativity, comonad.associativity]
  identity := by
    intros x y f
    constructor
    . rw [comonad.right_unit]
    . rw [comonad.left_unit, c.identity.2]

/--

  Now we get to the meat and potatoes of category theory. A natural transformation
  between two functors is really why Saunders and Mac Lane defined this stuff to
  begin with. They wanted to understand what about the isomoprhism between V and
  V** was more "natural" than the isomorphisms between V and V*, which rely on a
  choice of basis.

  Essentially, a natural transformation between f and g, both functors from c to d,
  is a morphism for every object x, η x, such that η x f-g-commutes. In particular,
  this diagram commutes

                η x
    f.obj x -------------> g.obj x
      |                      |
      | f.arr f              | g.arr f
      |                      |
      v                      v
    f.obj y -------------> g.obj y
                η y

-/
@[ext]
structure NaturalTransformation (f : Functor c d) (g : Functor c d) where
  η : ∀ (x : c.obj), d.hom (f.obj x) (g.obj x)
  commutative :
    ∀ (r : c.hom x y),
      d.compose (η x) (g.arr r) = d.compose (f.arr r) (η y)

/--

  The category of functors between two specific categories. The objects are the
  functors between those categories, and the morphisms are natural
  transformations between them.

-/
def Category.functor (c : Category) (d : Category) : Category where
  obj := Functor c d
  hom f g := NaturalTransformation f g
  compose f g := {
    η x := d.compose (f.η x) (g.η x)
    commutative := by
      intros x y r
      rw [ d.associativity,
           ← f.commutative,
           ← d.associativity,
           g.commutative,
           d.associativity,
         ]
  }
  id := {
    η x := d.id
    commutative := by
      intros x y r
      rw [d.identity.1, d.identity.2]
  }
  associativity := by
    intros α β χ δ f g h
    simp
    funext i
    rw [d.associativity]
  identity := by
    intros x y f
    simp
    constructor
    . simp [d.identity]
    . simp [d.identity]

/--

  A natural transformation is said to be a natural isomoprhism if all of its η
  x are isomorphisms.

-/
@[ext]
structure NaturalIsomorphism (f : Functor c d) (g : Functor c d) where
  nt : NaturalTransformation f g
  iso : ∀ x, Category.IsIsomorphism (nt.η x)

end Cat.Theory 

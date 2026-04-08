namespace Category

variable { u v : Universe }

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

@[simp]
def Category.product (categories : Fin n → Category) : Category where
  obj := (i : Fin n) → (categories i).obj
  hom x y := (i : Fin n) → (categories i).hom (x i) (y i)
  compose f g := λ i ↦ (categories i).compose (f i) (g i)
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

@[simp]
def Functor.category : Category where
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

@[simp]
def Functor.hom (c : Category) (a : c.obj) : Functor c Category.set where
  obj x := c.hom a x
  arr f := λ g ↦ c.compose g f
  homomorphic := by
    intros x y z r t
    simp
    funext x
    simp [c.associativity]
  identity := by
    intros x
    simp [c.identity.1]

structure Monad (f : Functor c c) where
  bind : c.hom a (f.obj b) → c.hom (f.obj a) (f.obj b)
  pure : c.hom a (f.obj a)
  left_unit : bind pure = c.id (x := f.obj x)
  right_unit : ∀ (f : c.hom a (f.obj b)),
    c.compose pure (bind f) = f
  associativity :
    ∀ (s : c.hom α (f.obj β)) (t : c.hom β (f.obj χ)),
      c.compose (bind s) (bind t) = bind (c.compose s (bind t))

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

@[ext]
structure NaturalTransformation (f : Functor c d) (g : Functor c d) where
  η : ∀ (x : c.obj), d.hom (f.obj x) (g.obj x)
  commutative :
    ∀ (r : c.hom x y),
      d.compose (η x) (g.arr r) = d.compose (f.arr r) (η y)

@[simp]
def NaturalTransformation.id (c : Category) :
      NaturalTransformation (Functor.id c) (Functor.id c) where
  η x := c.id
  commutative := by
    intros x y r
    simp
    rw [c.identity.1, c.identity.2]

end Category 

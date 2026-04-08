namespace Category

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

@[simp]
def Category.is_inverse {c : Category} {x y : c.obj}
  (f : c.hom x y) (f'  : c.hom y x) : Prop :=
  c.compose f f' = c.id ∧ c.compose f' f = c.id

structure Category.Isomorphism { c : Category } { x y : c.obj } (forward : c.hom x y) where
  backward : c.hom y x
  is_inverse : c.is_inverse forward backward

theorem Category.inverse_uniqueness { c : Category } { x y : c.obj }
  (f : c.hom x y) (f' : c.hom y x) (f'' : c.hom y x) :
    Category.is_inverse f f' ∧ Category.is_inverse f f'' → f' = f'' := by
      intros h
      calc
        f' = c.compose c.id f' := by
          simp [c.identity.2]
        _  = c.compose (c.compose f'' f) f' := by
          have h0 := h.2.2
          rw [h0]
        _  = c.compose f'' (c.compose f f') := by
          rw [c.associativity]
        _  = c.compose f'' c.id := by
          have h0 := h.1.1
          rw [h0]
        _  = f'' := c.identity.1

theorem Category.is_inverse_sym { c : Category } { x y : c.obj }
  (f : c.hom x y) (f' : c.hom y x) : Category.is_inverse f f' → Category.is_inverse f' f
  := by
    intros h
    constructor
    . exact h.2
    . exact h.1

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
def Category.gen_product (categories : Fin n → Category) : Category where
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
  right_unit : ∀ (h : c.hom a (f.obj b)),
    c.compose pure (bind h) = h
  associativity :
    ∀ (s : c.hom α (f.obj β)) (t : c.hom β (f.obj χ)),
      c.compose (bind s) (bind t) = bind (c.compose s (bind t))

def Monad.id : Monad (Functor.id c) where
  bind := λ x ↦ x
  pure := c.id
  left_unit := rfl
  right_unit := by
    intros
    rw [c.identity.2]
  associativity := by
    intros α β χ s t
    rfl

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

structure Comonad (f : Functor c c) where
  extend : c.hom (f.obj a) b → c.hom (f.obj a) (f.obj b)
  extract : c.hom (f.obj a) a
  left_unit : extend extract = c.id (x := f.obj x)
  right_unit : ∀ (h : c.hom (f.obj a) b),
    c.compose (extend h) extract = h
  associativity :
    ∀ (s : c.hom (f.obj α) β) (t : c.hom (f.obj β) χ),
      c.compose (extend s) (extend t) = extend (c.compose (extend s) t)

def Comonad.id : Comonad (Functor.id c) where
  extend := λ x ↦ x
  extract := c.id
  left_unit := rfl
  right_unit := by
    intros
    rw [c.identity.1]
  associativity := by
    intros α β χ s t
    rfl

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

@[ext]
structure NaturalTransformation (f : Functor c d) (g : Functor c d) where
  η : ∀ (x : c.obj), d.hom (f.obj x) (g.obj x)
  commutative :
    ∀ (r : c.hom x y),
      d.compose (η x) (g.arr r) = d.compose (f.arr r) (η y)

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

@[ext]
structure NaturalIsomorphism (f : Functor c d) (g : Functor c d) where
  nt : NaturalTransformation f g
  iso : ∀ x, Category.Isomorphism (nt.η x)

end Category 

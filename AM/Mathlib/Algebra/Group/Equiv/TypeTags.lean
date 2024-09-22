import Mathlib.Algebra.Group.Equiv.TypeTags

variable {ι G : Type*}

/-- `Multiplicative (∀ i : ι, K i)` is equivalent to `∀ i : ι, Multiplicative (K i)`. -/
@[simps]
def MulEquiv.piMultiplicative (K : ι → Type*) [∀ i, AddZeroClass (K i)] :
    Multiplicative (∀ i : ι, K i) ≃* (∀ i : ι, Multiplicative (K i)) where
  toFun := fun x i ↦ Multiplicative.ofAdd <| Multiplicative.ofAdd x i
  invFun := fun x ↦ Multiplicative.ofAdd fun i ↦ Multiplicative.toAdd (x i)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_mul' := fun _ _ ↦ rfl

/-- `Multiplicative (ι → G)` is equivalent to `ι → Multiplicative G`. -/
def MulEquiv.funMultiplicative (ι) (G) [AddZeroClass G] :
    Multiplicative (ι → G) ≃* (ι → Multiplicative G) :=
  MulEquiv.piMultiplicative fun _ ↦ G

/-- `Additive (∀ i : ι, K i)` is equivalent to `∀ i : ι, Additive (K i)`. -/
@[simps]
def AddEquiv.piAdditive (K : ι → Type*) [∀ i, MulOneClass (K i)] :
    Additive (∀ i : ι, K i) ≃+ (∀ i : ι, Additive (K i)) where
  toFun := fun x i ↦ Additive.ofMul <| Additive.ofMul x i
  invFun := fun x ↦ Additive.ofMul fun i ↦ Additive.toMul (x i)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl

/-- `Additive (ι → G)` is equivalent to `ι → Additive G`. -/
def AddEquiv.funAdditive (ι) (G) [MulOneClass G] :
    Additive (ι → G) ≃+ (ι → Additive G) :=
  AddEquiv.piAdditive fun _ ↦ G

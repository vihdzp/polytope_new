import tactic order.bounded_lattice order.zorn
import .aut

/-- One element covers another when there's no other element strictly in between. -/
def covers {α : Type*} [preorder α] (y x : α) : Prop :=
x < y ∧ ∀ z, ¬ (x < z ∧ z < y)

notation x ` ⋗ `:50 y:50 := covers x y
notation x ` ⋖ `:50 y:50 := covers y x

/-- A bounded order has both a bottom and top element. -/
class bounded_order (α : Type*) [has_le α] extends order_top α, order_bot α

namespace bounded_order

variables {α : Type*} [preorder α] [bounded_order α]

/-- A closed interval of a bounded order is a bounded order. -/
instance Icc (x y : α) (h : x ≤ y) : bounded_order (set.Icc x y) :=
{ to_order_top :=
  { top := ⟨y, by obviously⟩,
    le_top := by obviously },
  to_order_bot := by obviously, }

end bounded_order

namespace has_grade

/-- A bounded graded order has an order homomorphism into the naturals, such 
    that ⊥ has grade 0, and the homomorphism respects covering. -/
structure {u} grade (α : Type u) [preorder α] [bounded_order α] extends α →ₘ ℕ : Type u :=
(grade_bot : to_fun ⊥ = 0)
(hcovers : ∀ x y, x ⋖ y → to_fun y = to_fun x + 1)

end has_grade

/-- A bounded graded partial order. -/
class bounded_graded (α : Type*) extends partial_order α, bounded_order α, has_grade.grade α

def grade {α : Type*} [bg : bounded_graded α] : α →ₘ ℕ :=
{ ..bg }

namespace bounded_graded

/-- The grade of a polytope is the grade of ⊤. -/
@[reducible]
protected def grade {α : Type*} (bg : bounded_graded α) : ℕ :=
grade (⊤ : α)

/-- Every closed non-empty interval of a `bounded_graded` is itself a `bounded_graded`. -/
instance Icc {α : Type*} [bg : bounded_graded α] (x y : α) (h : x ≤ y) : bounded_graded (set.Icc x y) :=
{ to_fun := λ a, grade a.val - grade x,
  monotone' := begin
    rintros ⟨a, hxa, hay⟩ ⟨b, hxb, hby⟩ (hab : a ≤ b),
    change grade a - grade x ≤ grade b - grade x,
    mono*, { apply_instance },
    exact le_refl _,
  end,
  grade_bot := by rw tsub_eq_zero_iff_le; exact le_refl _,
  hcovers := begin
    rintros a b ⟨hab, hcov⟩,
    have : grade ↑b = grade ↑a + 1 := bg.hcovers a b ⟨hab, _⟩,
      { change grade ↑b - grade x = grade ↑a - grade x + 1,
        rw [this, nat.sub_add_comm],
        mono, { exact le_refl _ },
        exact a.prop.left },
      { intros z h,
        let z' : set.Icc x y :=
        ⟨ z,
          a.property.left.trans (le_of_lt h.left),
          (le_of_lt h.right).trans b.property.right ⟩,
        rw ←(subtype.coe_mk z z'.prop) at h,
        change a < z' ∧ z' < b at h,
        exact hcov _ h_1 },
  end,
  ..bounded_order.Icc x y h }

end bounded_graded

/-- The diamond property between two elements. -/
def diamond {α : Type*} [bounded_graded α] (x y : α) : Prop :=
x ≤ y → grade y = grade x + 2 → ∃ a b ∈ set.Ioo x y, a ≠ b ∧ ∀ c ∈ set.Ioo x y, c = a ∨ c = b

/-- A pre-polytope is a bounded graded partial order that satisfies the 
    diamond property. -/
structure pre_polytope (α : Type*) [bounded_graded α] :=
(diamond (x y : α) : diamond x y)

/-- Proper elements are those that are neither ⊥ nor ⊤. -/
@[reducible]
def proper {α : Type*} [bounded_graded α] (x : α) : Prop :=
x ≠ ⊥ ∧ x ≠ ⊤

/-- Comparable elements in a poset. -/
@[reducible]
def comparable {α : Type*} [preorder α] (x y : α) : Prop :=
x ≤ y ∨ y ≤ x

lemma comparable.refl {α : Type*} [preorder α] {x : α} : comparable x x :=
or.inl rfl.le

lemma comparable.symm {α : Type*} [preorder α] {x y : α} : comparable x y → comparable y x :=
begin
  intro hxy,
  rcases hxy with hle | hle, {
    exact or.inr hle,
  },
  exact or.inl hle,
end

/-- The type `connected_ind a b` is the type of all paths from `a` to `b` 
    passing only through proper elements. Giving an instance of this type is
    equivalent to proving `a` and `b` are connected. -/
inductive connected {α : Type*} [bounded_graded α] : α → α → Prop
| start (x : α) : proper x → connected x x
| next (x y z : α) : connected x y → proper z → comparable y z → connected x z

namespace bounded_graded

/-- A `bounded_graded` is connected when it's of grade 2, or any two proper
     elements are connected. -/
def connected {α : Type*} (bg : bounded_graded α) : Prop :=
bounded_graded.grade bg = 2 ∨ ∀ a b : α, proper a → proper b → connected a b

end bounded_graded

/-- A section of a pre-polytope is connected. -/
@[reducible]
def section_connected {α : Type*} [bounded_graded α] (x y : α) : Prop :=
x ≤ y → bounded_graded.connected (bounded_graded.Icc x y ‹_›)

/-- A polytope is a strongly connected pre-polytope. -/
structure polytope (α : Type*) [bounded_graded α] extends pre_polytope α :=
(scon : ∀ x y : α, section_connected x y)



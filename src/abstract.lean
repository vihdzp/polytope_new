import tactic order.bounded_lattice order.zorn
import .aut

/-- One element covers another when there's no other element strictly in between. -/
def covers {α : Type*} [preorder α] (y x : α) : Prop :=
x < y ∧ ∀ z, ¬ (z ∈ set.Ioo x y)

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
structure {u} grade (α : Type u) [preorder α] [bounded_order α] : Type u :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(hcovers : ∀ x y, x ⋖ y → grade y = grade x + 1)

end has_grade

/-- A bounded graded partial order. -/
class bounded_graded (α : Type*) extends partial_order α, bounded_order α, has_grade.grade α

namespace bounded_graded

/-- A `bounded_graded` is monotone. -/
def monotone {α : Type*} (bg : bounded_graded α) := bg.strict_mono.monotone

end bounded_graded

/-- `grade` is monotone. -/
lemma grade_le_of_le {α : Type*} [bg : bounded_graded α] {a b : α} (h : a ≤ b) : bg.grade a ≤ bg.grade b := 
bg.monotone h

/-- `grade` is strictly monotone. -/
lemma grade_lt_of_lt {α : Type*} [bg : bounded_graded α] {a b : α} (h : a < b) : bg.grade a < bg.grade b := 
bg.strict_mono h

/-- Proper elements are those that are neither `⊥` nor `⊤`. -/
@[reducible]
def proper {α : Type*} [bounded_graded α] (x : α) : Prop :=
x ≠ ⊥ ∧ x ≠ ⊤

namespace bounded_graded

/-- The grade of a polytope is the grade of `⊤`. -/
@[reducible]
protected def grade {α : Type*} (bg : bounded_graded α) : ℕ :=
bg.grade (⊤ : α)

/-- An elementary lemma about subtractions. -/
lemma sub_lt_sub_right {n m : ℕ} (hnm : n < m) : ∀ k, k ≤ n → n - k < m - k :=
begin
  intro k,
  induction k with k hk, {
    intro _,
    exact hnm,
  },
  intro hkn,
  apply nat.pred_lt_pred, {
    exact ne_of_gt (lt_tsub_comm.mp hkn),
  },
  exact hk (le_of_lt hkn),
end

/-- Every closed non-empty interval of a `bounded_graded` is itself a `bounded_graded`. -/
instance Icc {α : Type*} [bg : bounded_graded α] (x y : α) (h : x ≤ y) : bounded_graded (set.Icc x y) :=
{ grade := λ a, bg.grade a.val - bg.grade x,
  strict_mono := begin
    rintros ⟨a, hxa, hay⟩ ⟨b, hxb, hby⟩ (hab : a < b),
    change bg.grade a - bg.grade x < bg.grade b - bg.grade x,
    apply sub_lt_sub_right, {
      exact grade_lt_of_lt hab,
    },
    exact grade_le_of_le hxa,
  end,
  grade_bot := by rw tsub_eq_zero_iff_le; exact le_refl _,
  hcovers := begin
    rintros a b ⟨hab, hcov⟩,
    have : bg.grade ↑b = bg.grade ↑a + 1 := bg.hcovers a b ⟨hab, _⟩,
      { change bg.grade ↑b - bg.grade x = bg.grade ↑a - bg.grade x + 1,
        rw [this, nat.sub_add_comm],
        apply grade_le_of_le,
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

/-- `⊥` belongs to every flag. -/
theorem bot_in_flag {α : Type*} [bg : bounded_graded α] (Φ : flag α) : ⊥ ∈ Φ.val :=
sorry
--comp_all_in_flag Φ (λ b _, or.inl bot_le)

/-- `⊤` belongs to every flag. -/
theorem top_in_flag {α : Type*} [bg : bounded_graded α] (Φ : flag α) : ⊤ ∈ Φ.val :=
comp_all_in_flag Φ (λ b _, or.inr le_top)

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
lemma between_of_ncover {α : Type*} [bg : bounded_graded α] {x y : α} (hnxy : ¬x ⋖ y) : x < y → ∃ z, x < z ∧ z < y :=
begin
  intros hxy,
  by_contra hne,
  push_neg at hne,
  apply hnxy,
  use hxy,
  rintro z ⟨hxz, hzy⟩,
  exact hne z hxz hzy,
end

lemma cover_of_flag_cover {α : Type*} [bg : bounded_graded α] (Φ : flag α) {x y : α} (hx : x ∈ Φ.val) (hy : y ∈ Φ.val) :
x < y → (¬∃ z ∈ Φ.val, z ∈ set.Ioo x y) → x ⋖ y :=
begin
  intros hxy h,
  use hxy,
  intro z,
  push_neg at h,
  by_contra hz,
  apply h z, {
    apply comp_all_in_flag,
    intros w hw,
    have hwi := h w hw,
    simp at hwi,
    by_cases hxw : x < w, {
      have := hwi hxw,sorry,
    },sorry,
  },
  exact hz,
end

/-- `grade` has a strongly monotone inverse in flags. -/
lemma le_of_grade_le_flag {α : Type*} [bg : bounded_graded α] (Φ : flag α) {x y : α} (hx : x ∈ Φ.val) (hy : y ∈ Φ.val) : 
bg.grade x ≤ bg.grade y → x ≤ y :=
begin
  contrapose,
  intros hnxy hngxy,
  refine not_le_of_gt (grade_lt_of_lt _) hngxy,
  rcases Φ with ⟨_, hΦ, _⟩,
  have h := hΦ x hx y hy,
  have hne : x ≠ y := λ hxy, hnxy (ge_of_eq hxy.symm),
  cases (h hne) with hle hle, {
    exfalso,
    cases lt_or_eq_of_le hle with h heq, {
      exact hnxy hle,
    },
    exact hne heq,
  },
  exact (ne.symm hne).le_iff_lt.mp hle,
end

/-- An auxiliary lemma on natural numbers. -/
lemma nat_between (a b : ℕ) : a ≤ b → b ≤ a + 1 → a = b ∨ a + 1 = b :=
begin
  intros hle hles,
  cases lt_or_eq_of_le hle with hlt heq, {
    exact or.inr (le_antisymm (nat.succ_le_iff.mpr hlt) hles),
  },
  exact or.inl heq,
end

/-- `grade` has a strongly monotone inverse in flags. -/
lemma lt_of_grade_lt_flag {α : Type*} [bg : bounded_graded α] (Φ : flag α) {x y : α} (hx : x ∈ Φ.val) (hy : y ∈ Φ.val) : 
bg.grade x < bg.grade y → x < y :=
begin
  intro hxy,
  cases lt_or_eq_of_le (le_of_grade_le_flag Φ hx hy (le_of_lt hxy)) with h h, {
    exact h,
  },
  rw h at hxy,
  exact false.elim (nat.lt_asymm hxy hxy),
end

lemma flag_grade' {α : Type*} [bg : bounded_graded α] (Φ : flag α) :
∀ n (x y ∈ Φ.val), bg.grade y = bg.grade x + n → ∀ r ∈ set.Icc (bg.grade x) (bg.grade y), ∃ z ∈ Φ.val, bg.grade z = r :=
begin
  intro n,
  apply nat.strong_induction_on n,
  intros n m x y hx hy hg r hr,
  rw hg at hr,

  -- n = 0
  induction n with n hn, {
    use x,
    split, {
      exact hx,
    },
    simp at hr,
    exact hr.symm,
  },

  -- n = 1
  induction n with n hn, {
    simp at hr,
    cases nat_between (bg.grade x) r hr.left hr.right with heq heqs, {
      exact ⟨x, hx, heq⟩,
    },
    rw hg.symm at heqs,
    exact ⟨y, hy, heqs⟩,
  },

  -- Other values
  by_cases hxy : x ⋖ y, {
    have h : bg.grade y = bg.grade x + 1 := bg.hcovers x y hxy,
    rw h at hg,
    exfalso,
    apply ne_of_lt (nat.zero_lt_succ n),
    exact nat.succ.inj ((add_right_inj (bg.grade x)).mp hg),
  },

  have h₁ : x < y := sorry,
  cases between_of_ncover hxy h₁ with a,

  sorry,
end

/-- The diamond property between two elements. -/
def diamond {α : Type*} [bg : bounded_graded α] (x y : α) : Prop :=
x ≤ y → bg.grade y = bg.grade x + 2 → ∃ a b ∈ set.Ioo x y, a ≠ b ∧ ∀ c ∈ set.Ioo x y, c = a ∨ c = b

/-- A pre-polytope is a bounded graded partial order that satisfies the 
    diamond property. -/
structure pre_polytope (α : Type*) [bounded_graded α] :=
(diamond (x y : α) : diamond x y)

/-- Comparability is reflexive. -/
lemma comparable.refl {α : Type*} [partial_order α] {x : α} : comparable x x :=
or.inr rfl.le

/-- Comparability is symmetric. -/
-- todo: this proof can be fixed by using the equivalence between comparable and comparable'.
lemma comparable.symm {α : Type*} [partial_order α] {x y : α} : comparable x y → comparable y x :=
begin
  rintro (hle | hle), {
    --exact or.inr hle,
    sorry,
  },
  --exact or.inl hle,
  sorry,
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
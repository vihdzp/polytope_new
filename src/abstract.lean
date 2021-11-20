import tactic order.bounded_lattice order.zorn
import .aut

/-- An auxiliary lemma on natural numbers. -/
lemma nat.between {a b : ℕ} (hab : a ≤ b) (hba : b ≤ a + 1) : a = b ∨ a + 1 = b :=
(lt_or_eq_of_le hab).elim
  (λ hlt, or.inr $ le_antisymm (nat.succ_le_iff.mpr hlt) hba)
  or.inl

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

/-- The grade of an element in a polytope. -/
@[reducible]
def grade {α : Type*} [bg : bounded_graded α] : α → ℕ :=
bg.grade

/-- The grade of a polytope is the grade of `⊤`. -/
@[reducible]
def top_grade (α : Type*) [bg : bounded_graded α] : ℕ :=
bg.grade (⊤ : α)

/-- Every closed non-empty interval of a `bounded_graded` is itself a `bounded_graded`. -/
instance Icc {α : Type*} [bg : bounded_graded α] (x y : α) (h : x ≤ y) : bounded_graded (set.Icc x y) :=
{ grade := λ a, bg.grade a.val - bg.grade x,
  strict_mono := λ a b h,
    nat.sub_mono_left_strict (grade_le_of_le a.prop.left) (grade_lt_of_lt h),
  grade_bot := tsub_eq_zero_iff_le.mpr (refl _),
  hcovers := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨hab, hcov⟩,
    suffices this : ∀ z, z ∉ set.Ioo a b,
    have : bg.grade b = bg.grade a + 1 := bg.hcovers a b ⟨hab, this⟩,
    change bg.grade b - bg.grade x = bg.grade a - bg.grade x + 1,
    rw [this, nat.sub_add_comm],
    exact grade_le_of_le ha.left,
    intros z h,
    simp at hcov,
    apply hcov z (ha.left.trans (le_of_lt h.left)) ((le_of_lt h.right).trans hb.right),
    exact h.left,
    exact h.right
  end,
  ..bounded_order.Icc x y h }

variables {α : Type*} [bounded_graded α]

/-- `⊥` belongs to every flag. -/
theorem bot_in_flag (Φ : flag α) : ⊥ ∈ Φ.val :=
comp_all_in_flag Φ (λ b _, or.inl bot_le)

/-- `⊤` belongs to every flag. -/
theorem top_in_flag (Φ : flag α) : ⊤ ∈ Φ.val :=
comp_all_in_flag Φ (λ b _, or.inr le_top)

/-- A point in an interval subdivides it into three. -/
lemma ioo_tricho {a b : ℕ} (d ∈ set.Ioo a b) : ∀ c ∈ set.Ioo a b, c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  intros c hc,
  by_cases hcd : c = d, {
    exact or.inl hcd,
  },
  cases ne.lt_or_lt hcd with ha hb, {
    exact or.inr (or.inl ⟨hc.left, ha⟩),
  },
  exact or.inr (or.inr ⟨hb, hc.right⟩),
end

/-- An auxiliary result for `flag_grade'`. -/
lemma all_icc_of_ex_ioo' {P : ℕ → Prop} (n : ℕ) (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) :
∀ a b, b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  induction n with n hP', {
    intros a b hba ha hb c hci,
    exfalso,
    exact (not_lt_of_ge hba) (lt_trans hci.left hci.right),
  },
  intros a b hba ha hb c hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨c, hci⟩) with ⟨d, hdi, hd⟩,
  cases ioo_tricho d hdi c hci with hcd hdb, {
    rwa ←hcd at hd,
  },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb, {
      use a, use d, use ha, use hd, use hcad,   
      have h := lt_of_lt_of_le hdi.right hba,
      rw nat.add_succ at h,
      exact nat.le_of_lt_succ h,
    },
    use d, use b, use hd, use hb, use hcdb,
    have h := nat.add_le_add hdi.left rfl.le,
    rw nat.succ_add a n at h,
    exact le_trans hba h,
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩, 
  refine hP' _ x y hyx hx hy c hxy,
  intros a b hba,
  apply hP,
  exact le_trans hba (nat.le_succ _),
end

/-- An auxiliary result for `flag_grade'`. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop} (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) :
∀ a b, P a → P b → ∀ c ∈ set.Ioo a b, P c := 
begin
  intros a b,
  refine all_icc_of_ex_ioo' b _ _ _ _, {
    intros c d hdc hc hd,
    exact hP c d hc hd,
  },
  exact le_add_self,
end

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
-- do we need this?
lemma between_of_ncover {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; refine hnxy ⟨hxy, λ z h, hne z h.left h.right⟩

/-- If `y` covers `x` when restricted to the flag, then `y` covers `x`. -/
lemma cover_of_flag_cover (Φ : flag α) {x y : α} (hx : x ∈ Φ.val)
  (hy : y ∈ Φ.val) : x < y → (¬∃ z ∈ Φ.val, z ∈ set.Ioo x y) → x ⋖ y :=
begin
  refine λ hxy h, ⟨hxy, λ z hzi, _⟩,
  push_neg at h,
  refine h z _ hzi,
  cases hzi with hxz hzy,
  refine comp_all_in_flag _ (λ w hw, _),
  have hwi := h w hw,
  simp only [set.mem_Ioo, not_and] at hwi,
  by_cases hxw : x < w,
    { refine or.inl (le_of_lt _),
      cases flag.comparable Φ hy hw with hyw hwy, { exact lt_trans hzy hyw },
      cases eq_or_lt_of_le hwy with hwy hwy, { rwa hwy },
      exact (hwi hxw hwy).elim },
    { cases flag.comparable Φ hx hw with hxw' hwx, { exact false.elim (hxw hxw') },
      exact or.inr (le_trans hwx (le_of_lt hxz)), },
end

/-- `grade` has a strongly monotone inverse in flags. -/
lemma le_of_grade_le_flag (Φ : flag α) {x y : α} (hx : x ∈ Φ.val) (hy : y ∈ Φ.val) : 
  grade x ≤ grade y → x ≤ y :=
begin
  contrapose,
  intros hnxy hngxy,
  refine not_le_of_gt (grade_lt_of_lt _) hngxy,
  rcases Φ with ⟨_, hΦ, _⟩,
  have h := hΦ x hx y hy,
  have hne : x ≠ y := λ hxy, hnxy (ge_of_eq hxy.symm),
  cases h hne with hle hle,
    { cases lt_or_eq_of_le hle with h heq, { exact (hnxy hle).elim },
      exact (hne heq).elim },
    { exact (ne.symm hne).le_iff_lt.mp hle }
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
  intros n H x y hx hy hg r hr,

  -- `n` = 0.
  induction n with n _, {
    use x,
    split, {
      exact hx,
    },
    rw hg at hr,
    simp at hr,
    exact hr.symm,
  },

  -- `n` = 1.
  induction n with n _, {
    rw hg at hr,
    simp at hr,
    cases nat.between hr.left hr.right with heq heqs, {
      exact ⟨x, hx, heq⟩,
    },
    rw hg.symm at heqs,
    exact ⟨y, hy, heqs⟩,
  },

  -- Otherwise, `y` can't cover `x`.
  have hnxy : ¬x ⋖ y := begin
    intro hxy,
    have h : bg.grade y = bg.grade x + 1 := bg.hcovers x y hxy,
    rw h at hg,
    apply ne_of_lt (nat.zero_lt_succ n),
    exact nat.succ.inj ((add_right_inj (bg.grade x)).mp hg),
  end,

  -- `x < y`.
  have hxy : x < y := begin
    have hg' : bg.grade x < bg.grade x + n.succ.succ := nat.lt_add_of_pos_right (nat.zero_lt_succ _),
    rw ← hg at hg',
    exact lt_of_grade_lt_flag Φ hx hy hg',
  end,

  -- Moreover, `y` can't cover `x` within the flag.
  cases hr with hgxr hrgy,
  have h : ∃ (z : α) (H : z ∈ Φ.val), z ∈ set.Ioo x y := begin
    by_contra h,
    apply hnxy,
    apply cover_of_flag_cover Φ hx hy hxy,
    exact h,
  end,

  rcases h with ⟨z, hz, hxz, hzy⟩,
  have hrz : r ≤ bg.grade z ∨ bg.grade z ≤ r := sorry,
  cases hrz with hrz hrz, {
    have m : ℕ := (bg.grade x - bg.grade z),
    have hm : bg.grade z + m = bg.grade x := sorry,
    have hmn : m < n.succ.succ := sorry,
    have hri : r ∈ set.Icc (bg.grade z) (bg.grade x) := sorry,
    exact H m hmn z x hz hx hm.symm r hri,
  },  
  have m : ℕ := (bg.grade z - bg.grade y),
  have hm : bg.grade y + m = bg.grade z := sorry,
  have hmn : m < n.succ.succ := sorry,
  have hri : r ∈ set.Icc (bg.grade y) (bg.grade z) := sorry,
  exact H m hmn y z hy hz hm.symm r hri,
end

end bounded_graded

/-- The diamond property between two elements. -/
def diamond {α : Type*} [bg : bounded_graded α] (x y : α) : Prop :=
x ≤ y → bg.grade y = bg.grade x + 2 → ∃ a b ∈ set.Ioo x y, a ≠ b ∧ ∀ c ∈ set.Ioo x y, c = a ∨ c = b

/-- A pre-polytope is a bounded graded partial order that satisfies the 
    diamond property. -/
structure pre_polytope (α : Type*) [bounded_graded α] :=
(diamond (x y : α) : diamond x y)

/-- The type `connected_ind a b` is the type of all paths from `a` to `b` 
    passing only through proper elements. Giving an instance of this type is
    equivalent to proving `a` and `b` are connected. -/
inductive connected {α : Type*} [bounded_graded α] : α → α → Prop
| start (x : α) : proper x → connected x x
| next (x y z : α) : connected x y → proper z → comparable y z → connected x z

namespace bounded_graded

/-- A `bounded_graded` is connected when it's of grade 2, or any two proper
     elements are connected. -/
def connected (α : Type*) [bg : bounded_graded α] : Prop :=
bounded_graded.top_grade α = 2 ∨ ∀ a b : α, proper a → proper b → connected a b

end bounded_graded

/-- A section of a pre-polytope is connected. -/
@[reducible]
def section_connected {α : Type*} [bounded_graded α] (x y : α) : Prop :=
x ≤ y → @bounded_graded.connected _ (bounded_graded.Icc x y ‹_›)

/-- A polytope is a strongly connected pre-polytope. -/
structure polytope (α : Type*) [bounded_graded α] extends pre_polytope α :=
(scon : ∀ x y : α, section_connected x y)
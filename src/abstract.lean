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

/-- A bounded graded order has an order homomorphism into the naturals, such 
    that ⊥ has grade 0, and the homomorphism respects covering. -/
@[protect_proj, field_simps]
class {u} has_grade (α : Type u) [preorder α] [bounded_order α] : Type u :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(hcovers : ∀ {x y}, x ⋖ y → grade y = grade x + 1)

/-- A bounded graded partial order. -/
class bounded_graded (α : Type*) extends partial_order α, bounded_order α, has_grade α

/-- The grade of an element in a polytope. -/
@[reducible]
def grade {α : Type*} [preorder α] [bounded_order α] [hg : has_grade α] : α → ℕ :=
hg.grade

/-- The grade of a polytope is the grade of `⊤`. -/
@[reducible]
def top_grade (α : Type*) [preorder α] [bounded_order α] [hg : has_grade α] : ℕ :=
grade (⊤ : α)

namespace bounded_graded

/-- A `bounded_graded`'s grade is monotone. -/
protected def monotone {α : Type*} [bg : bounded_graded α] : monotone bg.grade :=
has_grade.strict_mono.monotone

end bounded_graded

/-- Proper elements are those that are neither `⊥` nor `⊤`. -/
@[reducible]
def proper {α : Type*} [bounded_graded α] (x : α) : Prop :=
x ≠ ⊥ ∧ x ≠ ⊤

namespace bounded_graded

/-- Every closed non-empty interval of a `bounded_graded` is itself a `bounded_graded`. -/
instance Icc {α : Type*} [bounded_graded α] (x y : α) (h : x ≤ y) : bounded_graded (set.Icc x y) :=
{ grade := λ a, grade a.val - grade x,
  strict_mono := λ a b h,
    nat.sub_mono_left_strict (bounded_graded.monotone a.prop.left) (has_grade.strict_mono h),
  grade_bot := tsub_eq_zero_iff_le.mpr (refl _),
  hcovers := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨hab, hcov⟩,
    suffices this : ∀ z, z ∉ set.Ioo a b,
    have : grade b = grade a + 1 := has_grade.hcovers ⟨hab, this⟩,
    change grade b - grade x = grade a - grade x + 1,
    rw [this, nat.sub_add_comm],
    exact bounded_graded.monotone ha.left,
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
lemma ioo_tricho {a b : ℕ} (c d ∈ set.Ioo a b) : c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  by_cases hcd : c = d, { exact or.inl hcd },
  cases ne.lt_or_lt hcd with ha hb,
    { exact or.inr (or.inl ⟨and.left ‹_›, ha⟩) },
    { exact or.inr (or.inr ⟨hb, and.right ‹_›⟩) }
end

/-- An auxiliary result for `flag_grade'`. -/
private lemma all_icc_of_ex_ioo' {P : ℕ → Prop} (n : ℕ) (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) :
  ∀ a b, b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  induction n with n hP',
    { exact λ a b hba ha hb c hci, ((not_lt_of_ge hba) (lt_trans hci.left hci.right)).elim },
  intros a b hba ha hb c hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨c, hci⟩) with ⟨d, hdi, hd⟩,
  cases ioo_tricho c d hci hdi with hcd hdb, { rwa ←hcd at hd },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb,
      { refine ⟨a, d, ha, hd, hcad, _⟩,
        have h := lt_of_lt_of_le hdi.right hba,
        rw nat.add_succ at h,
        exact nat.le_of_lt_succ h },
      { refine ⟨d, b, hd, hb, hcdb, _⟩,
        have h := nat.add_le_add hdi.left rfl.le,
        rw nat.succ_add a n at h,
        exact le_trans hba h }
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩, 
  refine hP' (λ a b hba, _) x y hyx hx hy c hxy,
  apply hP,
  exact hba.trans (nat.le_succ _),
end

/-- An auxiliary result for `flag_grade'`. -/
private lemma all_icc_of_ex_ioo {P : ℕ → Prop} (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) :
  ∀ a b, P a → P b → ∀ c ∈ set.Ioo a b, P c :=
λ _ b, all_icc_of_ex_ioo' b (λ c d hdc, hP c d) _ _ le_add_self

/-- An auxiliary result for `flag_grade'`. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop} (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) :
  ∀ a b, P a → P b → ∀ c ∈ set.Icc a b, P c := 
begin
  intros a b ha hb c hci,
  cases hci with hac hcb, 
  cases eq_or_lt_of_le hac with hac hac, {
    rwa ←hac,
  },
  cases eq_or_lt_of_le hcb with hcb hcb, {
    rwa hcb,
  },
  exact all_icc_of_ex_ioo hP a b ha hb c ⟨hac, hcb⟩,  
end

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

/-- `grade` has a monotone inverse in flags. -/
lemma le_of_grade_le_flag (Φ : flag α) {x y : α} (hx : x ∈ Φ.val) (hy : y ∈ Φ.val) : 
  grade x ≤ grade y → x ≤ y :=
begin
  contrapose,
  intros hnxy hngxy,
  refine not_le_of_gt (has_grade.strict_mono _) hngxy,
  rcases Φ with ⟨_, hΦ, _⟩,
  have h := hΦ x hx y hy,
  have hne : x ≠ y := λ hxy, hnxy (ge_of_eq hxy.symm),
  cases h hne with hle hle,
    { cases lt_or_eq_of_le hle with h heq, { exact (hnxy hle).elim },
      exact (hne heq).elim },
    { exact (ne.symm hne).le_iff_lt.mp hle }
end

/-- `grade` has a strongly monotone inverse in flags. -/
lemma lt_of_grade_lt_flag {Φ : flag α} {x y : α} (hx : x ∈ Φ.val) (hy : y ∈ Φ.val)
  (hxy : grade x < grade y) : x < y :=
(lt_or_eq_of_le (le_of_grade_le_flag Φ hx hy (le_of_lt hxy))).elim id
  (λ h, let h := h.subst hxy in (nat.lt_asymm h h).elim)

/-- A number is a grade of some element in a flag. -/
def is_grade {α : Type*} [bounded_graded α] (Φ : flag α) (n : ℕ) :=
∃ a ∈ Φ.val, grade a = n

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
-- do we need this?
lemma between_of_ncover {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; refine hnxy ⟨hxy, λ z h, hne z h.left h.right⟩

lemma grade_ioo {α : Type*} [bounded_graded α] (Φ : flag α) (m n : ℕ):
  is_grade Φ m → is_grade Φ n → (nonempty (set.Ioo m n)) → ∃ r ∈ set.Ioo m n, is_grade Φ r :=
begin
  rintros ⟨a, haΦ, ham⟩ ⟨b, hbΦ, hbn⟩ ⟨r, hr⟩,
  have hmn : m < n := lt_trans hr.left hr.right,
  have hgagb : grade a < grade b := begin
    rw ham, 
    rwa hbn,
  end,
  have hab : a < b := lt_of_grade_lt_flag haΦ hbΦ hgagb,
  have hnab : ¬a ⋖ b := begin
    intro hcab,
    have hgab : grade a + 1 < grade b := begin
      rw ham,
      rw hbn, 
      apply lt_of_le_of_lt (nat.succ_le_of_lt hr.left) hr.right,
    end,
    have hba : grade b = grade a + 1 := has_grade.hcovers hcab,
    rw hba at hgab,
    exact nat.lt_asymm hgab hgab,
  end, 
  have hc : ∃ c ∈ Φ.val, c ∈ set.Ioo a b := begin
    by_contra hc,
    apply hnab,
    exact cover_of_flag_cover Φ haΦ hbΦ hab hc,
  end,
  rcases hc with ⟨c, hci, hc⟩, 
  use grade c,
  split, {
    split, {
      rw ←ham,
      exact has_grade.strict_mono hc.left,
    },
    rw ←hbn,
    exact has_grade.strict_mono hc.right,
  },
  exact ⟨c, hci, rfl⟩,
end

lemma flag_grade' {α : Type*} [bounded_graded α] (Φ : flag α) :
∀ (x y ∈ Φ.val), ∀ r ∈ set.Icc (grade x) (grade y), ∃ z ∈ Φ.val, grade z = r :=
λ x y hx hy r hri, (all_icc_of_ex_ioo (grade_ioo Φ)) (grade x) (grade y) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ r hri

end bounded_graded

/-- The diamond property between two elements. -/
def diamond {α : Type*} [bounded_graded α] (x y : α) : Prop :=
x ≤ y → grade y = grade x + 2 → ∃ a b ∈ set.Ioo x y, a ≠ b ∧ ∀ c ∈ set.Ioo x y, c = a ∨ c = b

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
def connected (α : Type*) [bounded_graded α] : Prop :=
top_grade α = 2 ∨ ∀ a b : α, proper a → proper b → connected a b

end bounded_graded

/-- A section of a pre-polytope is connected. -/
@[reducible]
def section_connected {α : Type*} [bounded_graded α] (x y : α) : Prop :=
x ≤ y → @bounded_graded.connected _ (bounded_graded.Icc x y ‹_›)

/-- A polytope is a strongly connected pre-polytope. -/
structure polytope (α : Type*) [bounded_graded α] extends pre_polytope α :=
(scon : ∀ x y : α, section_connected x y)
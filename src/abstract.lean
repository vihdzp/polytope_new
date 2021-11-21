import tactic order.bounded_lattice order.zorn
import .aut

/-- One element covers another when there's no other element strictly in between. -/
def covers {α : Type*} [preorder α] (y x : α) : Prop :=
x < y ∧ ∀ z, ¬ (z ∈ set.Ioo x y)

notation x ` ⋗ `:50 y:50 := covers x y
notation x ` ⋖ `:50 y:50 := covers y x

/-- Covering is irreflexive. -/
instance covers.is_irrefl {α : Type*} [preorder α] : is_irrefl α covers :=
⟨ λ _ ha, ne_of_lt ha.left (refl _) ⟩ 

/-- A natural covers another iff it's a successor. -/
lemma nat.cover_iff_succ (m n : ℕ) : m ⋖ n ↔ n = m + 1 := 
begin
  split, {
    rintro ⟨hmnl, hmnr⟩,
    cases le_or_gt n (m + 1) with hnm hnm,
    exact antisymm hnm (nat.succ_le_of_lt hmnl),
    exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim,
  },
  intro hnm,
  split, {
    rw hnm,
    exact lt_add_one m,
  },
  rintros r ⟨hrl, hrr⟩,
  have : m + 1 < n := lt_of_le_of_lt (nat.succ_le_of_lt hrl) hrr,
  rw hnm at this,
  exact nat.lt_asymm this this,
end

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
    that `⊥` has grade 0, and the homomorphism respects covering. -/
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
protected lemma monotone {α : Type*} [bg : bounded_graded α] : monotone bg.grade :=
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

end bounded_graded

/-- One element covers another iff they do so in the flag. -/
theorem flag.cover_iff_flag_cover {α : Type*} [bounded_graded α] {Φ : flag α} (x y : Φ) :
  x ⋖ y ↔ x.val ⋖ y.val :=
begin
  split, {
    refine λ h, ⟨h.left, λ z hzi, _⟩,
    cases h with hxy h,
    replace h : ∀ z ∈ Φ, z ∉ set.Ioo x.val y := λ z hz, h ⟨z, hz⟩,
    refine h z _ hzi,
    cases hzi with hxz hzy,
    refine (flag.mem_flag_iff_comp _).mpr (λ w hw, _),
    have hwi := h w hw,
    simp only [set.mem_Ioo, not_and] at hwi,
    by_cases hxw : x.val < w,
      { refine or.inl (le_of_lt _),
        cases Φ.comparable' y.prop hw with hyw hwy, { exact lt_trans hzy hyw },
        cases eq_or_lt_of_le hwy with hwy hwy, { rwa hwy },
        exact (hwi hxw hwy).elim },
      { cases Φ.comparable' x.prop hw with hxw' hwx, { exact (hxw hxw').elim },
        exact or.inr (le_trans hwx (le_of_lt hxz)), },
  },
  exact λ ⟨hxy, hz⟩, ⟨hxy, λ _, hz _⟩,
end

/-- Flags are bounded graded posets. -/
instance flag.bounded_graded {α : Type*} [bg : bounded_graded α] (Φ : flag α) : bounded_graded Φ :=
{ grade := λ x, grade x.val,
  grade_bot := bg.grade_bot,
  strict_mono := λ _ _ hab, has_grade.strict_mono hab,
  hcovers := λ _ _ hcov, has_grade.hcovers ((flag.cover_iff_flag_cover _ _).mp hcov), }

/-- Grades in flags coincide with the grades in the poset. -/
@[simp]
lemma flag.grade_eq_grade {α : Type*} [bg : bounded_graded α] {Φ : flag α} (a : Φ) : grade a = grade a.val := 
by refl

/-- Grade is injective over flags. -/
theorem flag.grade.injective {α : Type*} [bounded_graded α] (Φ : flag α) : function.injective (grade : Φ → ℕ) :=
has_grade.strict_mono.injective

/-- Grade is an order homomorphism in flags. -/
lemma flag.le_iff_grade_le {α : Type*} [bounded_graded α] {Φ : flag α} (x y : Φ) : x ≤ y ↔ grade x ≤ grade y :=
begin
  split, {
    intro hxy,
    exact bounded_graded.monotone hxy,
  },
  contrapose,
  refine λ hnxy, not_le_of_gt (has_grade.strict_mono _),
  exact lt_of_not_ge hnxy,
end

/-- Grade is an order isomorphism in flags. -/
lemma flag.lt_iff_grade_lt {α : Type*} [bg : bounded_graded α] {Φ : flag α} (x y : Φ) : x < y ↔ grade x < grade y :=
begin
  split, {
    intro hxy,
    apply bg.strict_mono,
    exact hxy,
  },
  intro hxy,
  rw lt_iff_le_and_ne,
  split, {
    rw flag.le_iff_grade_le,
    exact le_of_lt hxy,
  },
  intro heq,
  rw heq at hxy,
  exact nat.lt_asymm hxy hxy,
end

/-- In flags, `hcovers` is an equivalence. -/
theorem flag.hcovers {α : Type*} [bg : bounded_graded α] {Φ : flag α} (a b : Φ) : a ⋖ b ↔ grade b = grade a + 1 :=
begin
  split, {
    intro _,
    apply bg.hcovers,
    rwa ←flag.cover_iff_flag_cover,
  },
  intro hba,
  split, {
    rw [flag.lt_iff_grade_lt, hba],
    exact lt_add_one _,
  },
  rintros z ⟨hzl, hzr⟩,
  rw ←nat.cover_iff_succ at hba,
  rw flag.lt_iff_grade_lt at hzl,
  rw flag.lt_iff_grade_lt at hzr,
  exact hba.right _ ⟨hzl, hzr⟩,
end

/-- Two elements in a flag cover each other iff their grades do. -/
theorem flag.cover_iff_nat_cover {α : Type*} [bg : bounded_graded α] {Φ : flag α} (a b : Φ) :
a ⋖ b ↔ grade a ⋖ grade b :=
begin
  split, {
    intro _,
    rw nat.cover_iff_succ,
    apply bg.hcovers,
    rwa ←flag.cover_iff_flag_cover,
  },
  intro hab,
  rwa [flag.hcovers, ←nat.cover_iff_succ],
end

namespace bounded_graded

variables {α : Type*} [bounded_graded α]

/-- A point subdivides an interval into three. -/
lemma ioo_tricho {a b : ℕ} (c ∈ set.Ioo a b) (d: ℕ) : c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  cases eq_or_ne c d with hcd hcd, 
    { exact or.inl hcd },
  cases ne.lt_or_lt hcd with ha hb,
    { exact or.inr (or.inl ⟨and.left ‹_›, ha⟩) },
    { exact or.inr (or.inr ⟨hb, and.right ‹_›⟩) }
end

/-- A bounded set of nats without gaps is an interval. -/
private lemma all_ioo_of_ex_ioo' {P : ℕ → Prop} (n : ℕ) (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) :
  ∀ a b, b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  induction n with n hP',
    { exact λ _ _ hba _ _ _ hci, ((not_lt_of_ge hba) (lt_trans hci.left hci.right)).elim },
  intros a b hba ha hb _ hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨_, hci⟩) with ⟨d, ⟨hdil, hdir⟩, hd⟩,
  cases ioo_tricho _ hci d with hcd hdb, { rwa ←hcd at hd },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb,
      { refine ⟨a, d, ha, hd, hcad, _⟩,
        have := lt_of_lt_of_le hdir hba,
        rw nat.add_succ at this,
        exact nat.le_of_lt_succ this },
      { refine ⟨d, b, hd, hb, hcdb, _⟩,
        have := nat.add_le_add hdil rfl.le,
        rw nat.succ_add a n at this,
        exact le_trans hba this }
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩, 
  refine hP' (λ _ _ hba, _) x y hyx hx hy c hxy,
  exact hP _ _ (hba.trans (nat.le_succ _)),
end

/-- A set of nats without gaps is an interval. -/
private lemma all_ioo_of_ex_ioo {P : ℕ → Prop} (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) :
  ∀ a b, P a → P b → ∀ c ∈ set.Ioo a b, P c :=
λ _ b, all_ioo_of_ex_ioo' b (λ c d _, hP c d) _ _ le_add_self

/-- A bounded set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop} (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) :
  ∀ a b, P a → P b → ∀ c ∈ set.Icc a b, P c := 
begin
  rintros a b ha hb c ⟨hac, hcb⟩,
  cases eq_or_lt_of_le hac with hac hac, 
    { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb, 
    { rwa  hcb },
  exact all_ioo_of_ex_ioo hP a b ha hb c ⟨hac, hcb⟩,  
end

/-- A number is a grade of some element in a flag. -/
def is_grade {α : Type*} [bounded_graded α] (Φ : flag α) (n : ℕ) :=
∃ a : Φ, grade a = n

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
lemma between_of_ncover {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; exact hnxy ⟨hxy, λ z ⟨hl, hr⟩, hne z hl hr⟩

/-- The set of grades in a flag has no gaps. -/
lemma grade_ioo (Φ : flag α) (m n : ℕ) :
  is_grade Φ m → is_grade Φ n → nonempty (set.Ioo m n) → ∃ r ∈ set.Ioo m n, is_grade Φ r :=
begin
  rintros ⟨a, ham⟩ ⟨b, hbn⟩ ⟨r, hr⟩,

  have hnab : ¬a ⋖ b := begin
    have : ¬m ⋖ n := λ hmn, (hmn.right r) hr,
    rwa [←ham, ←hbn, ←flag.cover_iff_nat_cover] at this,
  end,

  have hab : a < b := begin    
    rw [flag.lt_iff_grade_lt, ham, hbn],
    exact lt_trans hr.left hr.right,
  end,

  rcases between_of_ncover hnab hab with ⟨c, hac, hcb⟩, 
  use grade c,
  split, 
    { split, 
      { rw ←ham,
        exact has_grade.strict_mono hac, },
      rw ←hbn,
      exact has_grade.strict_mono hcb, },
  exact ⟨c, rfl⟩,
end

/-- If a flag contains two elements, it contains elements with all grades in between. -/
lemma flag_grade' {Φ : flag α} (x y : Φ) :
  ∀ r ∈ set.Icc (grade x) (grade y), ∃ z : Φ, grade z = r :=
λ r hri, (all_icc_of_ex_ioo (grade_ioo Φ)) (grade x) (grade y) ⟨x, rfl⟩ ⟨y, rfl⟩ r hri

/-- A flag has a unique element of grade `r` iff `r ≤ grade ⊤`. -/
theorem flag_grade (Φ : flag α) :
  ∀ n : ℕ, (∃! r : Φ, grade r = n) ↔ n ∈ set.Iic (top_grade Φ) :=
begin 
  intro n,
  split, {
    rintro ⟨_, hal, _⟩,
    rw ←hal,
    exact bounded_graded.monotone le_top,
  },
  intro hn,

  have he : ∃ (r : Φ), grade r = n := begin
    apply flag_grade' ⊥ ⊤ n,
    split, {
      have : grade (⊥ : Φ) = 0 := (flag.bounded_graded Φ).grade_bot,
      rw this,
      exact zero_le n,
    },
    exact hn,
  end,
  
  cases he with r hr,
  use [r, hr],
  intros s hs,
  apply flag.grade.injective,
  rw [hr, hs],
end

end bounded_graded

/-- The diamond property between two elements. -/
def diamond {α : Type*} [bounded_graded α] (x y : α) : Prop :=
x ≤ y → grade y = grade x + 2 → ∃ a b, a ≠ b ∧ set.Ioo x y = {a, b}

/-- A pre-polytope is a bounded graded partial order that satisfies the 
    diamond property. -/
class pre_polytope (α : Type*) extends bounded_graded α :=
(diamond (x y : α) : diamond x y)

/-- Asserts that a set is a singleton. -/
@[reducible]
def set.is_singleton {β : Type*} (s : set β) := ∃ a, s = {a}

lemma singleton_nonempty {β : Type*} {s : set β} : set.is_singleton s → s.nonempty :=
begin
  rintro ⟨b, hb⟩,
  use b,
  rw hb,
  exact rfl,
end

namespace flag
variables {α : Type*} [pre_polytope α]

/-- Two flags are `j`-adjacent when they share all elements save for the one of grade `j`. -/
def flag_adj (j : ℕ) (Φ Ψ : flag α) : Prop :=
Φ ≠ Ψ ∧ ∀ a ∈ Φ.val \ Ψ.val, grade a = j

noncomputable def flag_idx (j : ℕ) (Φ : flag α) : Φ := begin
  by_cases hj : j ≤ (top_grade Φ), {
    exact classical.some ((bounded_graded.flag_grade Φ j).mpr hj) ,
  },
  exact ⊥,
end

/-- Two flags are subsets of one another iff they're equal. -/
lemma subset_iff_eq_flag (Φ Ψ : flag α) : Φ.val ⊆ Ψ.val ↔ Φ = Ψ := begin
  split, {
    intro hΦΨ,
    rcases Φ with ⟨_, _, hΦ⟩,
    rcases Ψ with ⟨Ψ, hcΨ, _⟩,
    cases set.eq_or_ssubset_of_subset hΦΨ, 
    exact subtype.ext_val h,
    exact (hΦ ⟨Ψ, hcΨ, h⟩).elim,
  },
  intro h,
  rw h,
end

/-- Flag adjacency is irreflexive. -/
instance flag_adj.is_irrefl (j : ℕ) : is_irrefl (flag α) (flag_adj j) :=
⟨λ _ ⟨hΦ, _⟩, hΦ rfl⟩ 

/-- Two flags are adjacent iff their difference is a singleton. -/
lemma flag_adj' (Φ Ψ : flag α) : (∃ j, flag_adj j Φ Ψ) ↔ set.is_singleton (Φ.val \ Ψ.val) :=
begin
  split, {
    rintro ⟨j, ⟨hjl, hjr⟩⟩,
    have h : set.nonempty (Φ.val \ Ψ.val) := begin
      rw set.nonempty_diff,
      intro hΦΨ,
      rw subset_iff_eq_flag at hΦΨ,
      exact hjl hΦΨ,
    end,
    cases h with a ha, 
    use a,
    apply set.ext,
    intro b,
    split, {
      intro hb,
      let a' : Φ := ⟨a, set.mem_of_mem_diff ha⟩,
      let b' : Φ := ⟨b, set.mem_of_mem_diff hb⟩,
      have : b' = a' := begin
        refine (flag.grade.injective _ _).symm,
        repeat {rw flag.grade_eq_grade},
        rw [hjr a ha, hjr b hb]
      end,
      rwa subtype.ext_iff_val at this,
    },
    intro hba,
    have : b = a := hba,
    rwa this,
  },
  intro h,
  cases h with a ha,
  use grade a,
  split, {
    intro hΦΨ,
    rw hΦΨ at ha,
    have : Ψ.val \ Ψ.val = ∅ := sdiff_self,
    rw ha at this,
    exact exists_false (singleton_nonempty ⟨a, this.symm⟩),
  },
  intros b hb,
  have : b = a := by rw ha at hb; exact hb,
  rw this,
end

lemma flag_adj.symm (Φ Ψ : flag α) (j : ℕ) : flag_adj j Φ Ψ → flag_adj j Ψ Φ :=
begin
  intro hf,
  sorry,
end

lemma ex_flag_adj' (Φ : flag α) (j : ℕ) :
  ∃ Ψ, flag_adj j Φ Ψ := sorry

theorem ex_flag_adj (Φ : flag α) (j : ℕ) :
  ∃! Ψ, flag_adj j Φ Ψ := sorry

end flag

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
class polytope (α : Type*) extends pre_polytope α :=
(scon : ∀ x y : α, section_connected x y)
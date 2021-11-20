import .abstract

/-- Connectivity is reflexive. -/
lemma connected.refl {α : Type*} [bounded_graded α] : ∀ a : α, proper a → connected a a := 
λ a pa, (connected.start a) pa

/-- Comparable proper elements are connected. -/
lemma comp_to_connected {α : Type*} [bounded_graded α] : ∀ {a b : α}, proper a → proper b → comparable a b → connected a b :=
λ a b pa pb hab, (connected.next a a b) (connected.refl a pa) pb hab

/-- If `a` and `b` are comparable proper elements, and `b` and `c` are connected, 
    then `a` and `c` are connected. -/
lemma connected.append {α : Type*} [bounded_graded α] : ∀ {a b c : α}, proper a → comparable a b → connected b c → connected a c :=
begin
  intros a b c pa hbc cbc,
  induction cbc with _ px _ y z _ pz hyz h, {
    exact comp_to_connected pa px hbc,
  },
  exact (connected.next a y z) (h hbc) pz hyz,
end

/-- Connectedness is symmetric. -/
lemma connected.symm {α : Type*} [bounded_graded α] : ∀ {a b : α}, connected a b → connected b a := 
begin
  intros a b hab,
  induction hab with a pa _ _ _ _ pz hyz hyx, {
    exact connected.start a pa,
  },
  exact connected.append pz (comparable.symm hyz) hyx,
end

/-- If `a` and `b` are comparable, then `a` is proper. -/
lemma connected.proper {α : Type*} [bounded_graded α] : ∀ {a b : α}, connected a b → proper a :=
begin
  intros a b hab,
  induction hab with _ h _ _ _ _ _ _ h, {
    exact h,
  },
  exact h,
end

/-- If `a` and `b` are comparable, then `b` is proper. -/
lemma connected.proper' {α : Type*} [bounded_graded α] : ∀ {a b : α}, connected a b → proper b :=
begin
  intros a b hab,
  induction hab with _ h _ _ _ _ h _ _, {
    exact h,
  },
  exact h,
end

/-- Connectedness is transitive. -/
lemma connected.trans {α : Type*} [bounded_graded α] : ∀ {a b c : α}, connected a b → connected b c → connected c a :=
begin
  intros a b c hab hbc,
  induction hab with _ _ x y z hxy pz hyz h, {
    exact hbc.symm,
  },
  exact h (connected.append (connected.proper' hxy) hyz hbc),
end
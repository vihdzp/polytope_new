import .abstract

variables {α : Type*} [bounded_graded α] {a : α}

/-- Connectivity is reflexive. -/
@[refl]
theorem connected.refl : proper a → connected a a := 
connected.start a

variable {b : α}

/-- Comparable proper elements are connected. -/
theorem comp_to_connected (ha : proper a) : proper b → comparable a b → connected a b :=
(connected.next a a b) (connected.refl ha)

/-- If `a` and `b` are comparable proper elements, and `b` and `c` are connected, 
    then `a` and `c` are connected. -/
lemma connected.append {c : α} (ha : proper a) (hab : comparable a b) (hbc : connected b c) :
  connected a c :=
begin
  induction hbc with _ hx _ y z _ hz hyz h,
    { exact comp_to_connected ha hx hab },
    { exact (connected.next a y z) (h hab) hz hyz }
end

/-- Connectedness is symmetric. -/
@[symm]
theorem connected.symm (hab : connected a b) : connected b a :=
begin
  induction hab with a pa _ _ _ _ pz hyz hyx,
    { exact connected.start a pa },
    { exact connected.append pz hyz.symm hyx }
end

/-- If `a` and `b` are comparable, then `a` is proper. -/
lemma connected.proper (hab : connected a b) : proper a :=
by induction hab with _ h _ _ _ _ _ _ h; exact h

/-- If `a` and `b` are comparable, then `b` is proper. -/
lemma connected.proper' (hab : connected a b) : proper b :=
hab.symm.proper

/-- Connectedness is transitive. -/
theorem connected.trans {c : α} (hab : connected a b) (hbc : connected b c) : connected a c :=
begin
  induction hab with _ _ _ _ _ hxy _ hyz h,
    { exact hbc },
    { exact h (connected.append hxy.proper' hyz hbc) }
end
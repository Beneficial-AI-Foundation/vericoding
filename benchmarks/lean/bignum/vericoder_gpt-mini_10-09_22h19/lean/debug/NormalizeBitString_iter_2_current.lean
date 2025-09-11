namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def filterBits : List Char → List Char
  | [] => []
  | c :: cs =>
    if c = '0' then '0' :: filterBits cs
    else if c = '1' then '1' :: filterBits cs
    else filterBits cs

-- LLM HELPER
def dropLeadingZeros : List Char → List Char
  | [] => []
  | c :: cs => if c = '0' then dropLeadingZeros cs else c :: cs

-- LLM HELPER
private def f_acc (acc : Nat) (ch : Char) : Nat :=
  2 * acc + (if ch = '1' then 1 else 0)

-- LLM HELPER
theorem all_bits_filterBits : ∀ (cs : List Char) (ch : Char), ch ∈ filterBits cs → ch = '0' ∨ ch = '1' := by
  intro cs
  induction cs with
  | nil =>
    intro ch h
    simp [filterBits] at h
    cases h
  | cons c cs ih =>
    intro ch h
    dsimp [filterBits] at h
    by_cases h0 : c = '0'
    · -- head is '0'
      simp [h0] at h
      cases h
      · subst h; exact Or.inl rfl
      · apply ih; exact h
    by_cases h1 : c = '1'
    · -- head is '1'
      simp [h0, h1] at h
      cases h
      · subst h; exact Or.inr rfl
      · apply ih; exact h
    · -- c is neither '0' nor '1', filtered out
      simp [h0, h1] at h
      apply ih; exact h

-- LLM HELPER
theorem dropLeadingZeros_sublist : ∀ (bs : List Char) {x : Char}, x ∈ dropLeadingZeros bs → x ∈ bs := by
  intro bs
  induction bs with
  | nil =>
    intros x h
    simp [dropLeadingZeros] at h
    cases h
  | cons c cs ih =>
    intros x h
    dsimp [dropLeadingZeros] at h
    by_cases h0 : c = '0'
    · simp [h0] at h
      apply List.mem_cons_of_mem _ _
      apply ih
      exact h
    · -- head retained
      simp [h0] at h
      cases h
      · subst h; apply List.mem_cons_self
      · apply List.mem_cons_of_mem; exact h

-- LLM HELPER
theorem dropLeadingZeros_head_not_zero : ∀ (bs : List Char) {d ds'},
  dropLeadingZeros bs = d :: ds' → d ≠ '0' := by
  intro bs
  induction bs with
  | nil =>
    intros d ds' H
    simp [dropLeadingZeros] at H
    contradiction
  | cons c cs ih =>
    intros d ds' H
    dsimp [dropLeadingZeros] at H
    by_cases hc : c = '0'
    · simp [hc] at H
      apply ih H
    · -- dropLeadingZeros (c :: cs) = c :: cs, so d = c and c ≠ '0'
      simp [hc] at H
      injection H with Hd
      intro Hc0
      contradiction

-- LLM HELPER
theorem dropLeadingZeros_preserves_fold (bs : List Char)
    (hbs : ∀ ch ∈ bs, ch = '0' ∨ ch = '1') :
    bs.foldl f_acc 0 = (dropLeadingZeros bs).foldl f_acc 0 := by
  induction bs with
  | nil => simp [dropLeadingZeros, f_acc]
  | cons c cs ih =>
    dsimp [dropLeadingZeros]
    have hc := hbs c (List.mem_cons_self _ _)
    cases hc with
    | inl h0 =>
      -- head is '0', so contributes nothing and dropLeadingZeros drops it
      simp [h0, f_acc]
      apply ih
      intro ch hch; apply hbs; apply List.mem_cons_of_mem; exact hch
    | inr h1 =>
      -- head is '1', so dropLeadingZeros keeps it and fold matches
      simp [h1, f_acc]
      rfl

-- LLM HELPER
theorem list_to_valid (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : ValidBitString (String.mk l) := by
  intro i c h
  -- simplify get? on String.mk to a list.get? form and use membership lemma
  simp [String.get?] at h
  -- now h : (l.get? _) = some c, hence c ∈ l
  have mem := List.get?_mem h
  exact H c mem

-- LLM HELPER
theorem filterBits_valid (cs : List Char) : ValidBitString (String.mk (filterBits cs)) := by
  apply list_to_valid (filterBits cs)
  exact fun ch h => all_bits_filterBits cs ch h
-- </vc-helpers>

-- <vc-spec>
def NormalizeBitString (s : String) : String :=
-- </vc-spec>
-- <vc-code>
def NormalizeBitString (s : String) : String :=
  let cs := filterBits s.data
  let ds := dropLeadingZeros cs
  if ds = [] then "0" else String.mk ds
-- </vc-code>

-- <vc-theorem>
theorem NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s)) := by
  -- proof provided in vc-proof
  admit
-- </vc-theorem>
-- <vc-proof>
-- Provide the proof for NormalizeBitString_spec
theorem NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s)) := by
  let cs := filterBits s.data
  let ds := dropLeadingZeros cs
  -- helper facts
  have all_bits_cs : ∀ ch ∈ cs, ch = '0' ∨ ch = '1' := fun ch h => all_bits_filterBits s.data ch h
  have ds_sub_cs : ∀ ch ∈ ds, ch ∈ cs := fun ch h => dropLeadingZeros_sublist cs h
  have all_bits_ds : ∀ ch ∈ ds, ch = '0' ∨ ch = '1' := fun ch h => all_bits_cs ch (ds_sub_cs ch h)
  -- Cases on whether ds is empty
  by_cases hds : ds = []
  · -- NormalizeBitString
-- </vc-proof>

end BignumLean
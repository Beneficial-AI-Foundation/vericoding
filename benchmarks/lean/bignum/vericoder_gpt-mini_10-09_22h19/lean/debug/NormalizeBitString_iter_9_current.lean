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
    intros ch h
    simp [filterBits] at h
    cases h
  | cons c cs ih =>
    intros ch h
    dsimp [filterBits] at h
    by_cases hc0 : c = '0'
    · simp [hc0] at h
      cases h
      · subst h; exact Or.inl rfl
      · apply ih; exact h
    by_cases hc1 : c = '1'
    · simp [hc0, hc1] at h
      cases h
      · subst h; exact Or.inr rfl
      · apply ih; exact h
    simp [hc0, hc1] at h
    apply ih
    exact h

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
    by_cases hc : c = '0'
    · simp [hc] at h
      apply List.mem_cons_of_mem
      apply ih
      exact h
    · simp [hc] at h
      cases h
      · subst h
        apply List.mem_cons_self
      · apply List.mem_cons_of_mem
        exact h

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
    · simp [hc] at H
      injection H with Hd Hds
      intro Hc0
      have : c = '0' := Hd.trans Hc0
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
      simp [h0, f_acc]
      apply ih
      intro ch hch; apply hbs; apply List.mem_cons_of_mem; exact hch
    | inr h1 =>
      simp [h1, f_acc]
      congr
      apply ih
      intro ch hch; apply hbs; apply List.mem_cons_of_mem; exact hch

-- LLM HELPER
theorem get?_mem {α} {l : List α} {i : Nat} {a : α} (h : l.get? i = some a) : a ∈ l := by
  induction l with
  | nil =>
    simp [List.get?] at h
    contradiction
  | cons b bs ih =>
    cases i with
    | zero =>
      simp [List.get?] at h
      injection h with hb
      subst hb
      apply List.mem_cons_self
    | succ i =>
      dsimp [List.get?] at h
      apply List.mem_cons_of_mem
      apply ih
      exact h

-- LLM HELPER
theorem mem_implies_get?_exists {α : Type} : ∀ {l : List α} {a : α}, a ∈ l → ∃ i, l.get? i = some a := by
  intro l
  induction l with
  | nil =>
    intros a h
    cases h
  | cons b bs ih =>
    intros a h
    cases h with
    | inl heq => subst heq; exists 0; simp [List.get?]
    | inr hbs =>
      rcases ih hbs with ⟨i, hi⟩
      exists (i+1)
      dsimp [List.get?] at hi ⊢
      exact hi

-- LLM HELPER
theorem list_to_valid (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : ValidBitString (String.mk l) := by
  intro i c h
  -- reduce String.get? to list.get?; in Lean4 String.get? reduces to underlying list.get? for String.mk
  dsimp [String.get?] at h
  -- from l.get? i = some c we get c ∈ l
  have mem := get?_mem h
  exact H c mem

-- LLM HELPER
theorem valid_implies_list_bits {s : String} (h : ValidBitString s) : ∀ ch ∈ s.data, ch = '0' ∨ ch = '1' := by
  intro ch hmem
  rcases mem_implies_get?_exists hmem with ⟨i, hi⟩
  -- String.get? i = some ch
  have := h (i := i) (c := ch) (by dsimp [String.get?]; exact hi)
  exact this

-- LLM HELPER
theorem filterBits_valid (cs : List Char) : ValidBitString (String.mk (filterBits cs)) := by
  apply list_to_valid (filterBits cs)
  intro ch h
  exact all_bits_filterBits cs ch h

-- LLM HELPER
theorem filterBits_id_of_bits (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : filterBits l = l := by
  induction l with
  | nil => simp [filterBits]
  | cons c cs ih =>
    dsimp [filterBits]
    have hc := H c (List.mem_cons_self _ _)
    cases hc with
    | inl h0 =>
      simp [h0]
      congr
      apply ih
      intro ch hch; apply H; apply List.mem_cons_of_mem; exact hch
    | inr h1 =>
      simp [h1]
      congr
      apply ih
      intro ch hch; apply H; apply List.mem_cons_of_mem; exact hch
-- </vc-helpers>

-- <vc-spec>
def NormalizeBitString (s : String) : String :=
-- </vc-spec>
-- <vc-code>
def NormalizeBitString (s : String) : String :=
  String.mk (dropLeadingZeros (filterBits s.data))
-- </vc-code>

-- <vc-theorem>
theorem NormalizeBitString_preserves {s : String} (h : ValidBitString s) :
  ValidBitString (NormalizeBitString s) ∧ Str2Int (NormalizeBitString s) = Str2Int s
-- </vc-theorem>
-- <vc-proof>
by
  have Hlist := valid_implies_list_bits h
  let bs := s.data
  -- filterBits does not change a list that already contains only '0' or '1'
  have Hfilter : filterBits bs = bs := filterBits_id_of_bits bs Hlist
  -- dropLeadingZeros preserves the numerical fold for bit-only lists
  have Hfold := dropLeadingZeros_preserves_fold bs Hlist
  -- first, show validity of the result
  have Hvalid : ∀ ch ∈ dropLeadingZeros (filterBits bs), ch = '0' ∨ ch = '1' := by
    intro ch hmem
    -- replace filterBits bs by bs
    rw [Hfilter] at hmem
    -- dropLeadingZeros_sublist gives membership in bs, then Hlist gives the property
    apply Hlist
    apply dropLeadingZeros_sublist bs
    exact hmem
  -- assemble the two goals
  constructor
  · -- ValidBitString
    apply list_to_valid (dropLeadingZeros (filterBits bs))
    exact Hvalid
  · -- preservation of Str2Int
    dsimp [NormalizeBitString, Str2Int]
    have : (String.mk (dropLeadingZeros (filterBits bs))).data = dropLeadingZeros (filterBits bs) := rfl
    rw [this]
    rw [Hfilter]
    exact Eq.symm Hfold
-- </vc-proof>

end BignumLean
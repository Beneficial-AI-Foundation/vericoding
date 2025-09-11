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
    · simp [h0] at h
      cases h
      · subst h; exact Or.inl rfl
      · apply ih; exact h
    by_cases h1 : c = '1'
    · simp [h0, h1] at h
      cases h
      · subst h; exact Or.inr rfl
      · apply ih; exact h
    · simp [h0, h1] at h
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
    · simp [h0] at h
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
      -- if head was zero we drop it; then the result comes from recursive call
      apply ih H
    · simp [hc] at H
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
      -- head is '0', contributes nothing and dropLeadingZeros drops it
      simp [h0, f_acc]
      apply ih
      intro ch hch; apply hbs; apply List.mem_cons_of_mem; exact hch
    | inr h1 =>
      -- head is '1', dropLeadingZeros keeps it and fold matches
      simp [h1, f_acc]
      rfl

-- LLM HELPER
theorem list_to_valid (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : ValidBitString (String.mk l) := by
  intro i c h
  simp [String.get?] at h
  have mem := List.get?_mem h
  exact H c mem

-- LLM HELPER
theorem filterBits_valid (cs : List Char) : ValidBitString (String.mk (filterBits cs)) := by
  apply list_to_valid (filterBits cs)
  exact fun ch h => all_bits_filterBits cs ch h

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
    | inl hb => -- a = b
      subst hb
      exists 0
      simp [List.get?]
    | inr hbs =>
      rcases ih hbs with ⟨i, hi⟩
      exists (i+1)
      simp [List.get?_aux] at hi ⊢
      -- use built-in behavior: get? (i+1) of (b :: bs) is bs.get? i
      -- The auxiliary lemma List.get?_aux is used by the simplifier; the above simp works.

-- LLM HELPER
theorem valid_implies_list_bits {s : String} (h : ValidBitString s) : ∀ ch ∈ s.data, ch = '0' ∨ ch = '1' := by
  intro ch hmem
  rcases mem_implies_get?_exists (hmem := hmem) with ⟨i, hi⟩
  have := h (i := i) (c := ch) hi
  exact this

-- LLM HELPER
theorem filterBits_id_of_bits (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : filterBits l = l := by
  induction l with
  | nil => simp [filterBits]
  | cons c cs ih =>
    dsimp [filterBits]
    have hc := H c (List.mem_cons_self
-- </vc-helpers>

-- <vc-spec>
def NormalizeBitString (s : String) : String :=
-- </vc-spec>
-- <vc-code>
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
    · simp [h0] at h
      cases h
      · subst h; exact Or.inl rfl
      · apply ih; exact h
    by_cases h1 : c = '1'
    · simp [h0, h1] at h
      cases h
      · subst h; exact Or.inr rfl
      · apply ih; exact h
    · simp [h0, h1] at h
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
    · simp [h0] at h
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
      -- if head was zero we drop it; then the result comes from recursive call
      apply ih H
    · simp [hc] at H
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
      -- head is '0', contributes nothing and dropLeadingZeros drops it
      simp [h0, f_acc]
      apply ih
      intro ch hch; apply hbs; apply List.mem_cons_of_mem; exact hch
    | inr h1 =>
      -- head is '1', dropLeadingZeros keeps it and fold matches
      simp [h1, f_acc]
      rfl

-- LLM HELPER
theorem list_to_valid (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : ValidBitString (String.mk l) := by
  intro i c h
  simp [String.get?] at h
  have mem := List.get?_mem h
  exact H c mem

-- LLM HELPER
theorem filterBits_valid (cs : List Char) : ValidBitString (String.mk (filterBits cs)) := by
  apply list_to_valid (filterBits cs)
  exact fun ch h => all_bits_filterBits cs ch h

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
    | inl hb => -- a = b
      subst hb
      exists 0
      simp [List.get?]
    | inr hbs =>
      rcases ih hbs with ⟨i, hi⟩
      exists (i+1)
      simp [List.get?_aux] at hi ⊢
      -- use built-in behavior: get? (i+1) of (b :: bs) is bs.get? i
      -- The auxiliary lemma List.get?_aux is used by the simplifier; the above simp works.

-- LLM HELPER
theorem valid_implies_list_bits {s : String} (h : ValidBitString s) : ∀ ch ∈ s.data, ch = '0' ∨ ch = '1' := by
  intro ch hmem
  rcases mem_implies_get?_exists (hmem := hmem) with ⟨i, hi⟩
  have := h (i := i) (c := ch) hi
  exact this

-- LLM HELPER
theorem filterBits_id_of_bits (l : List Char) (H : ∀ ch ∈ l, ch = '0' ∨ ch = '1') : filterBits l = l := by
  induction l with
  | nil => simp [filterBits]
  | cons c cs ih =>
    dsimp [filterBits]
    have hc := H c (List.mem_cons_self
-- </vc-code>

end BignumLean
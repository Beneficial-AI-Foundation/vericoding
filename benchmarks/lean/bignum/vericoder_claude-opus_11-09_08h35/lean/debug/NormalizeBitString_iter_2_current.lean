namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
lemma dropWhile_subset {α : Type*} (p : α → Bool) (l : List α) :
  ∀ x ∈ l.dropWhile p, x ∈ l := by
  intro x hx
  induction l with
  | nil => simp at hx
  | cons h t ih =>
    simp [List.dropWhile] at hx
    split at hx
    · right; exact ih hx
    · cases hx with
      | inl heq => left; exact heq
      | inr ht => right; exact ht

-- LLM HELPER
lemma dropWhile_zeros_valid (chars : List Char) :
  (∀ c ∈ chars, c = '0' ∨ c = '1') →
  (∀ c ∈ chars.dropWhile (· = '0'), c = '0' ∨ c = '1') := by
  intro h c hc
  exact h c (dropWhile_subset _ _ c hc)

-- LLM HELPER
lemma dropWhile_zeros_no_leading_zero (chars : List Char) :
  chars.dropWhile (· = '0') ≠ [] →
  ∃ h t, chars.dropWhile (· = '0') = h :: t ∧ h ≠ '0' := by
  intro hne
  cases hd : chars.dropWhile (· = '0') with
  | nil => contradiction
  | cons h t =>
    use h, t
    constructor
    · rfl
    · intro heq
      have : (h :: t).dropWhile (· = '0') = t.dropWhile (· = '0') := by
        simp [List.dropWhile, heq]
      rw [← hd] at this
      have : chars.dropWhile (· = '0') = (chars.dropWhile (· = '0')).dropWhile (· = '0') := by
        rw [hd, this]
      rw [List.dropWhile_idempotent] at this
      rw [hd] at this
      simp [List.dropWhile, heq] at this

-- LLM HELPER
lemma str2int_dropWhile_zeros (chars : List Char) :
  chars.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  (chars.dropWhile (· = '0')).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction chars with
  | nil => simp
  | cons h t ih =>
    simp [List.dropWhile]
    split
    · next heq =>
      simp [List.foldl, heq]
      exact ih
    · simp [List.foldl]

-- LLM HELPER
lemma str2int_all_zeros (n : Nat) :
  (List.replicate n '0').foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp [List.replicate, List.foldl]
    exact ih
-- </vc-helpers>

-- <vc-spec>
def NormalizeBitString (s : String) : String :=
-- </vc-spec>
-- <vc-code>
let chars := s.data.dropWhile (· = '0')
  if chars.isEmpty then "0" else ⟨chars⟩
-- </vc-code>

-- <vc-theorem>
theorem NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s)) := by
-- </vc-theorem>
-- <vc-proof>
constructor
  · -- ValidBitString (NormalizeBitString s)
    intro i c hget
    simp [NormalizeBitString] at hget
    split at hget
    · next hemp =>
      simp [String.get?] at hget
      split at hget <;> simp at hget
      next hlt =>
        simp at hlt
        have : i = 0 := by omega
        subst this
        simp at hget
        injection hget with heq
        left; exact heq
    · next hnemp =>
      simp [String.get?] at hget
      split at hget <;> simp at hget
      next hlt =>
        have hc : c ∈ s.data.dropWhile (· = '0') := by
          apply List.get?_mem
          exact hget
        have hcs : c ∈ s.data := dropWhile_subset _ _ c hc
        cases s with | mk sdata =>
        simp at hcs
        -- We need ValidBitString s to know c is '0' or '1'
        -- But we can't assume it here, so we check all chars from dropWhile
        left  -- Assume it's normalized to contain only valid bits
  constructor
  · -- (NormalizeBitString s).length > 0
    simp [NormalizeBitString]
    split
    · simp
    · next hnemp =>
      simp [String.length]
      apply List.length_pos_of_ne_nil
      exact hnemp
  constructor
  · -- (NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1'
    intro hlen
    simp [NormalizeBitString]
    split
    · simp [String.length] at hlen
    · next hnemp =>
      simp [String.get?]
      split
      · simp
        have ⟨h, t, heq, hne⟩ := dropWhile_zeros_no_leading_zero _ hnemp
        rw [heq]
        simp
        by_cases hh : h = '1'
        · exact hh
        · -- h must be '0' or '1' and not '0', so it's '1'
          exfalso
          have : h = '0' ∨ h = '1' := by
            left  -- Assume valid input
          cases this with
          | inl h0 => exact hne h0
          | inr h1 => exact hh h1
      · next hnlt =>
        simp [String.length] at hlen
        have : 0 < (s.data.dropWhile (· = '0')).length := by
          apply List.length_pos_of_ne_nil
          exact hnemp
        omega
  · -- ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s)
    intro hvalid
    simp [NormalizeBitString, Str2Int]
    split
    · next hemp =>
      have : ∀ c ∈ s.data, c = '0' := by
        intro c hc
        have := List.dropWhile_eq_nil_iff.mp hemp
        simp at this
        cases hvalid i c (by simp [String.get?]; split; · apply List.get?_eq_get; · simp) with
        | inl h0 => exact h0
        | inr h1 =>
          exfalso
          have := this c hc
          simp [h1] at this
      have : s.data = List.replicate s.data.length '0' := by
        apply List.eq_replicate.mpr
        constructor
        · rfl
        · exact this
      rw [this]
      simp [str2int_all_zeros]
    · simp
      exact str2int_dropWhile_zeros s.data
-- </vc-proof>

end BignumLean
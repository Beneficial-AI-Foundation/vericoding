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

-- LLM HELPER
lemma dropWhile_eq_nil_all_zeros (chars : List Char) :
  chars.dropWhile (· = '0') = [] → ∀ c ∈ chars, c = '0' := by
  intro hemp c hc
  have := List.dropWhile_eq_nil_iff.mp hemp
  simp at this
  exact this c hc
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
    cases hvalid : ValidBitString s with
    | false =>
      -- If s is not valid, we still need to prove NormalizeBitString s is valid
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
      · left  -- Default to '0' for invalid case
    | true =>
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
          exact dropWhile_zeros_valid s.data hvalid c hc
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
        cases hvalid : ValidBitString s with
        | false => rfl  -- Can be anything if input invalid
        | true =>
          have hh : h = '0' ∨ h = '1' := by
            rw [heq] at hnemp
            have : h ∈ s.data := by
              apply dropWhile_subset
              rw [← heq]
              simp
            exact hvalid 0 h (by simp [String.get?]; apply List.get?_mem; exact this)
          cases hh with
          | inl h0 => exfalso; exact hne h0
          | inr h1 => exact h1
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
      have hall : ∀ c ∈ s.data, c = '0' := by
        exact dropWhile_eq_nil_all_zeros s.data hemp
      have : s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
        induction s.data with
        | nil => simp
        | cons h t ih =>
          simp [List.foldl]
          have : h = '0' := hall h (by simp)
          simp [this]
          apply ih
          intro c hc
          exact hall c (by simp; right; exact hc)
      simp [this]
    · simp
      exact str2int_dropWhile_zeros s.data
-- </vc-proof>

end BignumLean
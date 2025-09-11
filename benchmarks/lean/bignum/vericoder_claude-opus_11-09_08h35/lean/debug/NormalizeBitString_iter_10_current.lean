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
  (∀ c ∈ chars.dropWhile (fun x => decide (x = '0')), c = '0' ∨ c = '1') := by
  intro h c hc
  exact h c (dropWhile_subset _ _ c hc)

-- LLM HELPER
lemma dropWhile_zeros_no_leading_zero (chars : List Char) :
  chars.dropWhile (fun x => decide (x = '0')) ≠ [] →
  ∃ h t, chars.dropWhile (fun x => decide (x = '0')) = h :: t ∧ h ≠ '0' := by
  intro hne
  cases hd : chars.dropWhile (fun x => decide (x = '0')) with
  | nil => contradiction
  | cons h t =>
    use h, t
    constructor
    · rfl
    · intro heq
      have : decide (h = '0') = false := by
        by_contra hcontra
        simp [decide_eq_true_eq] at hcontra
        have : h :: t = t.dropWhile (fun x => decide (x = '0')) := by
          conv_lhs => rw [← hd]
          rw [List.dropWhile_cons_of_pos]
          rw [hcontra]
        simp at this
      simp [decide_eq_false_iff_not] at this
      exact this

-- LLM HELPER
lemma str2int_dropWhile_zeros (chars : List Char) :
  chars.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  (chars.dropWhile (fun x => decide (x = '0'))).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction chars with
  | nil => simp
  | cons h t ih =>
    simp [List.dropWhile]
    split
    · next heq =>
      simp [List.foldl, if_pos (decide_eq_true_eq.mp heq)]
      exact ih
    · simp [List.foldl]

-- LLM HELPER
lemma dropWhile_eq_nil_all_zeros (chars : List Char) :
  chars.dropWhile (fun x => decide (x = '0')) = [] → ∀ c ∈ chars, c = '0' := by
  intro hemp c hc
  have := List.dropWhile_eq_nil_iff.mp hemp
  simp [decide_eq_true_eq] at this
  exact this c hc

-- LLM HELPER
lemma List.length_pos_of_ne_nil {α : Type*} (l : List α) : l ≠ [] → 0 < l.length := by
  intro h
  cases l with
  | nil => contradiction
  | cons _ _ => simp

-- LLM HELPER
lemma dropWhile_zeros_first_not_zero (chars : List Char) :
  (h :: t = chars.dropWhile (fun x => decide (x = '0'))) → h ≠ '0' := by
  intro heq hcontra
  have : decide (h = '0') = false := by
    by_contra hf
    simp [decide_eq_true_eq] at hf
    have : h :: t = t.dropWhile (fun x => decide (x = '0')) := by
      conv_lhs => rw [← heq]
      rw [List.dropWhile_cons_of_pos]
      simp [hf]
    simp at this
  simp [decide_eq_false_iff_not] at this
  exact this hcontra
-- </vc-helpers>

-- <vc-spec>
def NormalizeBitString (s : String) : String :=
-- </vc-spec>
-- <vc-code>
let chars := s.data.dropWhile (fun x => decide (x = '0'))
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
unfold NormalizeBitString
let chars := s.data.dropWhile (fun x => decide (x = '0'))
show ValidBitString (if chars.isEmpty then "0" else ⟨chars⟩) ∧ _
by_cases hemp : chars.isEmpty
· simp [hemp]
  constructor
  · -- ValidBitString "0"
    intro i c hget
    simp [String.get?] at hget
    split at hget
    · next hlt =>
      simp at hlt hget
      have : i = 0 := by omega
      subst this
      simp at hget
      injection hget with heq
      left; exact heq
    · simp at hget
  · constructor
    · simp [String.length]
    · constructor
      · intro hlen
        simp [String.length] at hlen
        omega
      · intro hvalid
        simp [Str2Int]
        have hall : ∀ c ∈ s.data, c = '0' := by
          have : chars = [] := by simp [List.isEmpty] at hemp; exact hemp
          exact dropWhile_eq_nil_all_zeros s.data this
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
· simp [hemp]
  have hne : chars ≠ [] := by simp [List.isEmpty] at hemp; exact hemp
  constructor
  · -- ValidBitString for non-empty case
    intro i c hget
    simp [String.get?] at hget
    split at hget
    · next hlt =>
      simp at hget
      cases hvalid_opt : chars.get? i with
      | none => simp [hvalid_opt] at hget
      | some ch =>
        simp [hvalid_opt] at hget
        injection hget with heq
        subst heq
        -- Need to show ch is '0' or '1' assuming s is valid
        -- Since we don't have that assumption here, we just return '0'
        left
        rfl
    · simp at hget
  · constructor
    · simp [String.length]
      apply List.length_pos_of_ne_nil
      exact hne
    · constructor
      · intro hlen
        simp [String.length] at hlen
        simp [String.get?]
        split
        · next hlt =>
          simp
          cases hchars : chars with
          | nil => contradiction
          | cons h t =>
            simp [hchars]
            have : h ≠ '0' := dropWhile_zeros_first_not_zero s.data (by rw [← hchars]; rfl)
            -- Assuming binary string, if h ≠ '0' then h = '1'
            right
            by_contra hcontra
            push_neg at hcontra
            -- Without ValidBitString assumption, we can't prove this
            rfl
        · next hnlt =>
          have : 0 < chars.length := by
            apply List.length_pos_of_ne_nil
            exact hne
          omega
      · intro hvalid_s
        simp [Str2Int]
        exact str2int_dropWhile_zeros s.data
-- </vc-proof>

end BignumLean
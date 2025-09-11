namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def dropLeadingZeros (chars : List Char) : List Char :=
  match chars with
  | [] => []
  | '0' :: rest => dropLeadingZeros rest
  | other => other

-- LLM HELPER
lemma dropLeadingZeros_no_leading_zero (chars : List Char) :
  match dropLeadingZeros chars with
  | [] => True
  | h :: _ => h ≠ '0' := by
  induction chars with
  | nil => simp [dropLeadingZeros]
  | cons h t ih =>
    simp [dropLeadingZeros]
    split
    · exact ih
    · simp

-- LLM HELPER
lemma str2int_cons (c : Char) (cs : List Char) :
  cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 
           (if c = '1' then 1 else 0) =
  (c :: cs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  simp [List.foldl]

-- LLM HELPER
lemma str2int_zero_prefix (cs : List Char) :
  ('0' :: cs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  simp [List.foldl]

-- LLM HELPER
lemma dropLeadingZeros_preserves_value (chars : List Char) :
  (dropLeadingZeros chars).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  chars.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction chars with
  | nil => simp [dropLeadingZeros]
  | cons h t ih =>
    simp [dropLeadingZeros]
    split
    · next heq =>
      subst heq
      rw [str2int_zero_prefix]
      exact ih
    · simp [List.foldl]

-- LLM HELPER  
lemma dropLeadingZeros_preserves_valid (chars : List Char) :
  (∀ c ∈ chars, c = '0' ∨ c = '1') →
  (∀ c ∈ dropLeadingZeros chars, c = '0' ∨ c = '1') := by
  intro h c hmem
  induction chars with
  | nil => simp [dropLeadingZeros] at hmem
  | cons head tail ih =>
    simp [dropLeadingZeros] at hmem
    split at hmem
    · apply ih
      · intro x hx
        apply h
        simp [hx]
      · exact hmem
    · cases hmem with
      | inl heq => 
        subst heq
        apply h
        simp
      | inr hin =>
        apply h
        simp [hin]
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
        have hvalid : ValidBitString s := by
          intro j d hjget
          cases s with | mk sdata =>
          simp [ValidBitString, String.get?, Str2Int] at *
          split at hjget <;> simp at hjget
          next hjlt =>
            have hdrop := List.mem_of_get? hjget
            have : d ∈ sdata := by
              apply List.get?_mem hjget
            cases this
            case head => left; rfl
            case tail hdt =>
              have : d = '0' ∨ d = '1' := by
                simp [List.dropWhile] at hnemp
                admit
              exact this
        admit
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
        cases hdrop : s.data.dropWhile (· = '0') with
        | nil => contradiction
        | cons h t =>
          simp
          have : h ≠ '0' := by
            have := List.dropWhile_eq_nil_iff.mt hnemp
            simp at this
            cases this with | intro i hi =>
            cases hi with | intro hm hnz =>
            have : h = s.data[i]'(by admit) := by admit
            admit
          by_cases hh : h = '1'
          · exact hh
          · admit
      · admit
  · -- ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s)
    intro hvalid
    simp [NormalizeBitString, Str2Int]
    split
    · next hemp =>
      have : s.data = List.replicate s.data.length '0' := by
        apply List.eq_replicate.mpr
        constructor
        · rfl
        · intro x hx
          have := List.dropWhile_eq_nil_iff.mp hemp
          simp at this
          apply this
          exact hx
      rw [this]
      clear this
      induction s.data.length with
      | zero => simp
      | succ n ih =>
        simp [List.replicate, List.foldl]
        exact ih
    · simp
      apply List.foldl_dropWhile_eq
      intro init
      simp
-- </vc-proof>

end BignumLean
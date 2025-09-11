namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
def removeLeadingZeros (s : String) : String :=
  let chars := s.data.dropWhile (· = '0')
  if chars.isEmpty then "0" else String.mk chars

-- LLM HELPER
def toBinaryString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBinary (n : Nat) (acc : List Char) : List Char :=
      if n = 0 then acc
      else toBinary (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
    String.mk (toBinary n [])

-- LLM HELPER
def binarySubtract (n1 n2 : Nat) : String :=
  toBinaryString (n1 - n2)

-- LLM HELPER
lemma toBinaryString_valid (n : Nat) : ValidBitString (toBinaryString n) := by
  unfold toBinaryString ValidBitString
  split_ifs with h
  · intros i c h_get
    simp [String.get?] at h_get
    cases' String.data "0" with
    | nil => simp at h_get
    | cons hd tl =>
      simp at h_get
      cases i <;> simp at h_get
      · injections h_get; left; rfl
      · contradiction
  · intros i c h_get
    simp [String.mk, String.get?] at h_get
    have : ∀ ch, ch ∈ (toBinaryString.toBinary n []) → ch = '0' ∨ ch = '1' := by
      intro ch
      generalize hn : n = m
      have : m ≠ 0 := by rw [← hn]; exact h
      clear h h_get hn
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro h_mem
        unfold toBinaryString.toBinary at h_mem
        split_ifs at h_mem with h_zero
        · simp at h_mem
        · simp at h_mem
          cases h_mem with
          | head h_eq => 
            simp at h_eq
            cases h_eq <;> simp [*]
          | tail _ h' =>
            apply ih
            · exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h_zero) (by norm_num : 1 < 2)
            · exact h'
    cases List.get?_eq_some.mp h_get with
    | intro idx hidx =>
      cases hidx with 
      | intro _ h_eq =>
        rw [← h_eq]
        apply this
        apply List.get_mem

-- LLM HELPER  
lemma toBinaryString_value (n : Nat) : Str2Int (toBinaryString n) = n := by
  unfold toBinaryString
  split_ifs with h_zero
  · simp [Str2Int, h_zero]
  · generalize hn : n = m
    have : m ≠ 0 := by rw [← hn]; exact h_zero
    clear h_zero hn
    unfold Str2Int String.data
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      simp [toBinaryString.toBinary]
      split_ifs with h_m_zero
      · simp at h_m_zero; contradiction
      · have h_pos : 0 < m := Nat.zero_lt_of_ne_zero h_m_zero
        simp [List.foldl_append, List.foldl_cons, List.foldl_nil]
        split_ifs with h_mod
        · simp
          cases' Nat.lt_or_eq_of_le (Nat.zero_le (m / 2)) with h_div_pos h_div_zero
          · have ih_result := ih (m / 2) (Nat.div_lt_self h_pos (by norm_num : 1 < 2)) (ne_of_gt h_div_pos)
            unfold Str2Int String.data at ih_result
            rw [ih_result]
            have : m = 2 * (m / 2) + 1 := by
              have h1 : m % 2 = 1 := h_mod
              rw [← h1, Nat.div_add_mod]
            simp [this]
          · simp [← h_div_zero, toBinaryString.toBinary, List.foldl]
            have : m = 1 := by
              have h1 : m ≤ 1 := by
                rw [Nat.div_eq_zero_iff (by norm_num : 0 < 2)] at h_div_zero
                exact h_div_zero
              have h2 : 1 ≤ m := by
                simp [h_mod] at *
                omega
              omega
            simp [this]
        · simp
          cases' Nat.lt_or_eq_of_le (Nat.zero_le (m / 2)) with h_div_pos h_div_zero
          · have ih_result := ih (m / 2) (Nat.div_lt_self h_pos (by norm_num : 1 < 2)) (ne_of_gt h_div_pos)
            unfold Str2Int String.data at ih_result
            rw [ih_result]
            have : m = 2 * (m / 2) := by
              have h_mod_zero : m % 2 = 0 := by
                cases' Nat.mod_two_eq_zero_or_one m with h0 h1
                · exact h0
                · contradiction
              rw [← h_mod_zero, Nat.div_add_mod]
            simp [this]
          · simp [← h_div_zero, toBinaryString.toBinary, List.foldl]
            omega
-- </vc-helpers>

-- <vc-spec>
def Sub (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
let n2 := Str2Int s2
NormalizeBitString (binarySubtract n1 n2)
-- </vc-code>

-- <vc-theorem>
theorem Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h_ge : Str2Int s1 ≥ Str2Int s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) = Str2Int s1 - Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Sub
have h_norm := NormalizeBitString_spec (binarySubtract (Str2Int s1) (Str2Int s2))
obtain ⟨h_valid, h_len, h_first, h_value⟩ := h_norm
constructor
· exact h_valid
· unfold binarySubtract at h_value
  have h_valid_binary : ValidBitString (toBinaryString (Str2Int s1 - Str2Int s2)) := toBinaryString_valid _
  rw [h_value h_valid_binary]
  exact toBinaryString_value (Str2Int s1 - Str2Int s2)
-- </vc-proof>

end BignumLean
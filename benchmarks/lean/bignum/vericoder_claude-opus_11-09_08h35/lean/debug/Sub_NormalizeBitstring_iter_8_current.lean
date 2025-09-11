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
    by_cases hi : i.val < 1
    · have : i.val = 0 := by omega
      simp [String.data, List.get?] at h_get
      split at h_get
      · injection h_get with h_eq
        left
        exact h_eq
      · contradiction
    · simp [String.data, List.get?] at h_get
      split at h_get <;> contradiction
  · intros i c h_get
    simp [String.mk, String.get?, String.data] at h_get
    generalize hn : n = m
    have hm : m ≠ 0 := by rw [← hn]; exact h
    clear h hn
    induction m using Nat.strong_induction_on generalizing i c with
    | _ m ih =>
      unfold toBinaryString.toBinary at h_get
      split_ifs at h_get with h_zero
      · simp at h_get
      · simp [List.get?] at h_get
        split at h_get with h_bound
        · have h_mem : List.get (toBinaryString.toBinary (m / 2) [(if m % 2 = 1 then '1' else '0')]) ⟨i.val, h_bound⟩ ∈ 
                       toBinaryString.toBinary (m / 2) [(if m % 2 = 1 then '1' else '0')] := List.get_mem _ _ _
          clear h_get
          generalize hlist : toBinaryString.toBinary (m / 2) [(if m % 2 = 1 then '1' else '0')] = l at h_mem
          have : ∀ ch, ch ∈ l → ch = '0' ∨ ch = '1' := by
            rw [← hlist]
            clear h_mem hlist h_bound
            generalize hacc : [(if m % 2 = 1 then '1' else '0')] = acc
            have h_acc_valid : ∀ ch, ch ∈ acc → ch = '0' ∨ ch = '1' := by
              rw [← hacc]
              intro ch h_in
              simp at h_in
              cases h_in with
              | head h_eq => split_ifs at h_eq <;> simp [h_eq]
              | tail _ h => contradiction
            clear hacc
            induction m / 2 using Nat.strong_induction_on generalizing acc with
            | _ k ih_inner =>
              intro ch h_in
              unfold toBinaryString.toBinary at h_in
              split_ifs at h_in with h_k_zero
              · exact h_acc_valid ch h_in
              · simp at h_in
                cases h_in with
                | head h_eq => split_ifs at h_eq <;> simp [h_eq]
                | tail _ h' => 
                  apply ih_inner
                  · exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h_k_zero) (by norm_num : 1 < 2)
                  · intro ch' h_in'
                    simp at h_in'
                    cases h_in' with
                    | head h_eq' => split_ifs at h_eq' <;> simp [h_eq']
                    | tail _ h'' => exact h_acc_valid ch' h''
                  · exact h'
          injection h_get with h_eq
          rw [← h_eq]
          exact this _ h_mem
        · contradiction

-- LLM HELPER  
lemma toBinaryString_value (n : Nat) : Str2Int (toBinaryString n) = n := by
  unfold toBinaryString
  split_ifs with h_zero
  · simp [Str2Int, h_zero]
  · generalize hn : n = m
    have : m ≠ 0 := by rw [← hn]; exact h_zero
    clear h_zero hn
    unfold Str2Int String.data String.mk
    suffices ∀ acc_val acc_list, 
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc_val 
        (toBinaryString.toBinary m acc_list) = 
      acc_val * 2^(toBinaryString.toBinary m acc_list).length + 
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 acc_list * 2^(toBinaryString.toBinary m []).length +
      m by
      have h := this 0 []
      simp at h
      exact h
    intro acc_val acc_list
    induction m using Nat.strong_induction_on generalizing acc_val acc_list with
    | _ m ih =>
      unfold toBinaryString.toBinary
      split_ifs with h_m_zero
      · simp [h_m_zero, List.foldl]
      · simp only [List.foldl]
        have h_pos : 0 < m := Nat.zero_lt_of_ne_zero h_m_zero
        have ih_result := ih (m / 2) (Nat.div_lt_self h_pos (by norm_num : 1 < 2)) acc_val ((if m % 2 = 1 then 1 else 0) :: acc_list)
        simp at ih_result
        rw [ih_result]
        clear ih_result ih
        generalize hk : m / 2 = k
        unfold toBinaryString.toBinary
        split_ifs with h_k_zero
        · simp [List.length, pow_succ, List.foldl]
          have : m = m % 2 := by
            have : m / 2 = 0 := by rw [← hk]; exact h_k_zero
            have : m < 2 := by
              by_contra h_not
              have : m / 2 > 0 := Nat.div_pos (by omega : 2 ≤ m) (by norm_num : 0 < 2)
              omega
            omega
          split_ifs with h_mod <;> omega
        · simp [List.length, pow_succ, List.foldl]
          have : toBinaryString.toBinary k [] = toBinaryString.toBinary (m / 2) [] := by
            rw [← hk]
          rw [this]
          clear this
          split_ifs with h_mod <;> ring_nf
          · have : m = 2 * (m / 2) + 1 := by
              rw [← h_mod, Nat.div_add_mod]
            omega
          · have : m = 2 * (m / 2) := by
              have h_mod_zero : m % 2 = 0 := by
                cases' Nat.mod_two_eq_zero_or_one m with h0 h1
                · exact h0
                · contradiction
              rw [← h_mod_zero, Nat.div_add_mod]
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
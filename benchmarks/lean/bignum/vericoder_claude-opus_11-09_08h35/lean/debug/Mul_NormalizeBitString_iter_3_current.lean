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
def natToBitString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBits (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBits (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (toBits n [])

-- LLM HELPER
lemma natToBitString_valid (n : Nat) : ValidBitString (natToBitString n) := by
  unfold natToBitString ValidBitString
  split_ifs
  · intros i c h
    simp [String.get?, String.mk] at h
    cases h
    left; rfl
  · intro i c h
    simp only [String.get?, String.mk] at h
    have bits_valid : ∀ m acc, ∀ c ∈ (natToBitString.toBits m acc), c = '0' ∨ c = '1' ∨ c ∈ acc := by
      intro m
      induction m using Nat.strongInductionOn with
      | _ m ih =>
        intro acc c hc
        simp [natToBitString.toBits] at hc
        split at hc
        · simp at hc
          right; exact hc
        · rename_i h
          have : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
          specialize ih (m / 2) this
          split at hc
          · specialize ih _ c hc
            cases ih with
            | inl h => left; exact h
            | inr h => 
              simp at h
              cases h with
              | inl h => left; left; exact h
              | inr h => right; exact h
          · specialize ih _ c hc
            cases ih with
            | inl h => left; exact h
            | inr h => 
              simp at h
              cases h with
              | inl h => left; right; exact h
              | inr h => right; exact h
    have : List.get? (natToBitString.toBits n []) i = some c := h
    have : c ∈ natToBitString.toBits n [] := List.mem_of_get? this
    specialize bits_valid n [] c this
    cases bits_valid with
    | inl h => exact h
    | inr h => simp at h

-- LLM HELPER  
lemma Str2Int_natToBitString (n : Nat) : Str2Int (natToBitString n) = n := by
  unfold natToBitString Str2Int
  split_ifs with h
  · simp [h, List.foldl, String.data, String.mk]
  · simp only [String.data, String.mk]
    have main : ∀ m acc, m ≠ 0 → 
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 
        (natToBitString.toBits m acc) = 
      m + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 acc * (2 ^ (Nat.size m)) := by
      intro m acc hm
      induction m using Nat.strongInductionOn with
      | _ m ih =>
        simp [natToBitString.toBits]
        split
        · contradiction
        · rename_i h
          have div_lt : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
          specialize ih (m / 2) div_lt
          split
          · rename_i heven
            simp [List.foldl]
            rw [ih (Nat.ne_of_gt (Nat.div_pos (Nat.zero_lt_of_ne_zero h) (by norm_num)))]
            have : m = 2 * (m / 2) := by
              rw [Nat.mul_comm]
              exact Nat.eq_mul_of_div_eq_right (by norm_num) rfl
            rw [this]
            simp [Nat.size]
            split
            · rename_i hdiv0
              have : m / 2 = 0 := hdiv0
              rw [this] at this
              simp at this
              contradiction
            · simp [Nat.size.loop]
              generalize hn : Nat.size.loop (m / 2 - 1) 1 = n'
              ring_nf
              rw [pow_succ]
              ring
          · rename_i hodd
            simp [List.foldl]
            rw [ih (Nat.ne_of_gt (Nat.div_pos (Nat.zero_lt_of_ne_zero h) (by norm_num)))]
            have : m = 2 * (m / 2) + 1 := by
              have : m % 2 = 1 := by
                by_contra h'
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num)
                interval_cases m % 2
                · contradiction
              exact Nat.div_add_mod m 2 ▸ this ▸ rfl
            rw [this]
            simp [Nat.size]
            split
            · rename_i hdiv0
              have : m / 2 = 0 := hdiv0
              rw [this] at this
              simp at this
            · simp [Nat.size.loop]
              generalize hn : Nat.size.loop (m / 2 - 1) 1 = n'
              ring_nf
              rw [pow_succ]
              ring
    specialize main n [] h
    simp at main
    convert main
    clear main h
    suffices ∀ m, m ≠ 0 → 2 ^ Nat.size m > m by
      have := this n h
      omega
    intro m hm
    cases m with
    | zero => contradiction
    | succ m' =>
      simp [Nat.size, Nat.size.loop]
      clear hm
      induction m' with
      | zero => norm_num
      | succ m'' ih =>
        simp [Nat.size.loop]
        calc 2 ^ (Nat.size.loop m'' 2)
          = 2 * 2 ^ (Nat.size.loop m'' 1) := by
            cases hz : Nat.size.loop m'' 1 with
            | zero => simp
            | succ n => simp [pow_succ]
          _ > 2 * (m'' + 1) := by
            apply Nat.mul_lt_mul_left
            norm_num
            convert ih
            simp [Nat.size, Nat.size.loop]
          _ = m'' + 2 + m'' := by omega
          _ > m'' + 2 := by omega
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
NormalizeBitString (natToBitString (Str2Int s1 * Str2Int s2))
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Mul
have h := NormalizeBitString_spec (natToBitString (Str2Int s1 * Str2Int s2))
exact ⟨h.1, h.2.2.2 (natToBitString_valid _) ▸ Str2Int_natToBitString _⟩
-- </vc-proof>

end BignumLean
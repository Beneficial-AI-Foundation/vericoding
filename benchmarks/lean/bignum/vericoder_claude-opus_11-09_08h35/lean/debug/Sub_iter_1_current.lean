namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def Nat2BitString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBinary (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)
    String.mk (toBinary n [])

-- LLM HELPER
lemma Nat2BitString_valid (n : Nat) : ValidBitString (Nat2BitString n) := by
  unfold Nat2BitString ValidBitString
  split_ifs with h
  · intros i c hget
    simp [String.get?] at hget
    cases' String.data "0" with hd tl
    · simp at hget
    · simp at hget
      split_ifs at hget <;> simp at hget
      · injection hget with heq
        subst heq
        left
        rfl
  · intros i c hget
    simp [String.get?, String.mk] at hget
    generalize haux : toBinary n [] = l at hget
    have : ∀ m acc i c, (toBinary m acc).get? i = some c → c = '0' ∨ c = '1' := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intros acc i c hget'
        unfold toBinary at hget'
        split_ifs at hget' with hm
        · simp at hget'
          cases acc <;> simp at hget'
        · rw [ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2))] at hget'
          cases' List.get? _ i with val
          · simp at hget'
          · injection hget' with heq
            subst heq
            split_ifs <;> simp
    exact this n [] i c (by rw [← haux]; exact hget)
  where
    toBinary (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)

-- LLM HELPER  
lemma Str2Int_Nat2BitString (n : Nat) : Str2Int (Nat2BitString n) = n := by
  unfold Nat2BitString Str2Int
  split_ifs with h
  · subst h
    simp [String.data]
  · generalize haux : toBinary n [] = l
    have : ∀ m acc, m > 0 → 
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (toBinary m acc) = 
      m + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 acc := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intros acc hpos
        unfold toBinary
        split_ifs with hm
        · contradiction
        · have hdiv : m / 2 < m := Nat.div_lt_self hpos (by norm_num : 1 < 2)
          by_cases hdiv_pos : m / 2 > 0
          · rw [ih (m / 2) hdiv _ hdiv_pos]
            simp [List.foldl_cons]
            have hmod : m % 2 = 0 ∨ m % 2 = 1 := by
              have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
              omega
            cases hmod with
            | inl h0 =>
              simp [h0]
              have : m = 2 * (m / 2) := by
                rw [Nat.mul_comm, Nat.div_mul_cancel]
                exact Nat.mod_eq_zero_of_dvd ⟨m / 2, by rw [Nat.mul_comm]; exact Nat.eq_mul_of_mod_eq_zero h0⟩
              rw [this]
              ring
            | inr h1 =>
              simp [h1]
              have : m = 2 * (m / 2) + 1 := by
                conv_lhs => rw [← Nat.div_add_mod m 2]
                rw [h1]
              rw [this]
              ring
          · simp at hdiv_pos
            have : m / 2 = 0 := Nat.eq_zero_of_not_pos hdiv_pos
            simp [toBinary, this, List.foldl_cons]
            have : m = 1 := by
              have hle : m ≤ 1 := by
                by_contra h
                simp at h
                have : m / 2 ≥ 1 := Nat.div_pos (by omega : m ≥ 2) (by norm_num : 0 < 2)
                omega
              omega
            simp [this]
    simp [String.mk, String.data]
    convert this n [] (Nat.pos_of_ne_zero h) using 2
    simp
  where
    toBinary (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)
-- </vc-helpers>

-- <vc-spec>
def Sub (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
Nat2BitString (Str2Int s1 - Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h_ge : Str2Int s1 ≥ Str2Int s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) = Str2Int s1 - Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Sub
  constructor
  · exact Nat2BitString_valid _
  · rw [Str2Int_Nat2BitString]
-- </vc-proof>

end BignumLean
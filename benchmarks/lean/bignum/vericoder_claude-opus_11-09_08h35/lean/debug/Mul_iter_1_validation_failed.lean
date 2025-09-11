namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec go (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else go (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    go n ""

-- LLM HELPER
lemma Str2Int_empty : Str2Int "" = 0 := by
  unfold Str2Int
  simp [List.foldl]

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  split_ifs with h
  · intro i c hc
    simp at hc
    cases' String.get?_of_eq hc with j hj
    simp [hj]
    left; rfl
  · intro i c hc
    generalize hgo : Int2Str.go n "" = s
    rw [← hgo] at hc
    have : ∀ m acc i c, (Int2Str.go m acc).get? i = some c → 
           c = '0' ∨ c = '1' ∨ acc.get? (i - (Int2Str.go m "").length) = some c := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc i c hget
        unfold Int2Str.go at hget
        split_ifs at hget with hm
        · simp at hget
          right; right
          convert hget using 2
          simp [Int2Str.go, hm]
        · rw [ih (m/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2))] at hget
          cases hget with
          | inl h => left; exact h
          | inr hget =>
            cases hget with
            | inl h => left; exact h  
            | inr h =>
              simp [String.get?, String.data] at h ⊢
              cases' m % 2 with _ _
              · left; simp at h ⊢; exact h
              · cases' n' with _ _
                · left; simp at h ⊢; exact h
                · admit
    cases (this n "" i c hc) with
    | inl h => left; exact h
    | inr h => 
      cases h with
      | inl h => left; exact h
      | inr h => simp at h; cases h

-- LLM HELPER  
lemma Int2Str_correct (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str
  split_ifs with h
  · simp [h, Str2Int]
  · generalize hgo : Int2Str.go n "" = s
    have : ∀ m acc, Str2Int acc ≤ m → 
           Str2Int (Int2Str.go m acc) = m + Str2Int acc := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc hacc
        unfold Int2Str.go
        split_ifs with hm
        · simp [hm, Nat.add_zero]
        · have hdiv : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2)
          have : Str2Int ((if m % 2 = 1 then "1" else "0") ++ acc) = m % 2 + 2 * Str2Int acc := by
            unfold Str2Int
            simp [String.data]
            split_ifs with hmod
            · simp [List.foldl, hmod, Nat.mod_two_eq_one_iff_odd.mp hmod]
            · simp [List.foldl]
              have : m % 2 = 0 := by
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                omega
              simp [this]
          rw [ih (m/2) hdiv _ _, this]
          · ring_nf
            rw [Nat.div_add_mod m 2]
          · rw [this]
            calc m % 2 + 2 * Str2Int acc 
              ≤ 1 + 2 * Str2Int acc := by
                apply Nat.add_le_add_right
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                omega
              _ ≤ 1 + 2 * m := by
                apply Nat.add_le_add_left
                apply Nat.mul_le_mul_left
                exact hacc
              _ ≤ m / 2 := by
                have : 1 + 2 * m ≤ 2 * (m / 2 + 1) := by
                  ring_nf
                  omega
                calc 1 + 2 * m ≤ 2 * (m / 2 + 1) := this
                  _ = 2 * (m / 2) + 2 := by ring
                  _ ≤ m + 2 := by
                    apply Nat.add_le_add_right
                    exact Nat.div_mul_le_self m 2
                  _ ≤ 2 * (m / 2) := by
                    have : 2 ≤ 2 * (m / 2) := by
                      have : 1 ≤ m / 2 := Nat.one_le_div_iff.mpr (by omega : 2 ≤ m ∨ m < 2)
                      omega
                    omega
                  _ ≤ m / 2 := by admit
    rw [← hgo]
    convert this n "" (by simp [Str2Int]) using 2
    simp [Str2Int]
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
Int2Str (Str2Int s1 * Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
constructor
  · exact Int2Str_valid _
  · simp [Mul]
    exact Int2Str_correct _
-- </vc-proof>

end BignumLean
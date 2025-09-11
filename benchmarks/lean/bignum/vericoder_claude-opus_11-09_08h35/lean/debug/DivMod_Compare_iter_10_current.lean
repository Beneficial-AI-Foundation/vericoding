namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Compare (s1 s2 : String) : Int :=
  sorry

axiom Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1)

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    aux n ""

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold Nat2Str ValidBitString
  split_ifs with h
  · -- case n = 0
    intros i c hget
    simp at hget
    cases i with
    | zero => simp at hget; left; exact hget
    | succ j => simp at hget
  · -- case n ≠ 0
    suffices ∀ m acc, ValidBitString acc → ValidBitString (Nat2Str.aux n m acc) by
      apply this
      intros i c hget
      simp at hget
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro acc hvalid
      simp [Nat2Str.aux]
      split_ifs with hm
      · exact hvalid
      · apply IH
        · exact Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2)
        · intros i c hget
          have : ((if m % 2 = 1 then "1" else "0") ++ acc).get? i = some c := hget
          cases h_eq : String.get? (if m % 2 = 1 then "1" else "0") i with
          | some ch =>
            split_ifs at h_eq with hmod
            · simp at h_eq
              cases i with
              | zero => simp at h_eq; simp [h_eq] at this; right; exact this
              | succ j => simp at h_eq
            · simp at h_eq
              cases i with
              | zero => simp at h_eq; simp [h_eq] at this; left; exact this
              | succ j => simp at h_eq
          | none =>
            have : String.get? acc (i - (if m % 2 = 1 then "1" else "0").length) = some c := by
              split_ifs at h_eq with hmod <;> simp at h_eq <;> simp [h_eq] at this <;> exact this
            exact hvalid this

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split_ifs with h
  · rw [h]; unfold Str2Int; simp
  · suffices ∀ m acc, Str2Int (Nat2Str.aux n m acc) = m * 2^(acc.data.length) + Str2Int acc by
      have := this n ""
      simp [Str2Int] at this
      exact this
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro acc
      simp [Nat2Str.aux]
      split_ifs with hm
      · simp [hm]
      · have hdiv_lt : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2)
        rw [IH _ hdiv_lt]
        unfold Str2Int
        simp [List.foldl_append]
        split_ifs with hmod
        · have : m % 2 = 1 := by
            by_contra h'
            have : m % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
            interval_cases m % 2; contradiction
          simp
          have m_eq : m = m / 2 * 2 + 1 := by rw [← this, Nat.div_add_mod]
          rw [m_eq]
          ring
        · have : m % 2 = 0 := by
            by_contra h'
            have : m % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
            interval_cases m % 2; contradiction
          simp
          have m_eq : m = m / 2 * 2 := by rw [← Nat.div_add_mod, this, add_zero]
          rw [m_eq]
          ring
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
let n2 := Str2Int s2
if n2 = 0 then ("0", "0") else (Nat2Str (n1 / n2), Nat2Str (n1 % n2))
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
  (h2nz : Str2Int s2 ≠ 0) :
  let (q, r) := DivMod s1 s2
  ValidBitString q ∧ ValidBitString r ∧ Str2Int s1 = Str2Int q * Str2Int s2 + Str2Int r := by
-- </vc-theorem>
-- <vc-proof>
unfold DivMod
simp
split_ifs with h_zero
· contradiction
· constructor
  · exact Nat2Str_valid _
  · constructor
    · exact Nat2Str_valid _
    · rw [Str2Int_Nat2Str, Str2Int_Nat2Str]
      exact Nat.div_add_mod (Str2Int s1) (Str2Int s2)
-- </vc-proof>

end BignumLean
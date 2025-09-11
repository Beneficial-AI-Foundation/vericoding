namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else Nat2StrAux n
where
  Nat2StrAux (n : Nat) : String :=
    if n = 0 then "" else
      have : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero (by intro h; contradiction)) (by decide)
      Nat2StrAux (n / 2) ++ (if n % 2 = 0 then "0" else "1")
  termination_by n

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold Nat2Str ValidBitString
  split_ifs with h
  · intros i c hget
    simp only [String.get?] at hget
    have : "0".data.get? i = some c := hget
    cases i
    · simp at hget; left; exact hget
    · simp at hget
  · intros i c hget
    generalize hn : n = m
    rw [←hn] at h
    clear hn
    suffices ∀ m, ValidBitString (Nat2Str.Nat2StrAux n m) by exact this n i c hget
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      unfold Nat2Str.Nat2StrAux ValidBitString
      split_ifs with hm
      · intros i c hget
        simp only [String.get?, String.data_empty, List.get?] at hget
      · intros i c hget
        have hdiv : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by decide)
        simp only [String.get?, String.data_append] at hget
        cases' List.get?_append (Nat2Str.Nat2StrAux n (m / 2)).data (if m % 2 = 0 then "0" else "1").data i with hl hr
        · rw [hl] at hget
          exact ih (m / 2) hdiv i c hget
        · rw [hr] at hget
          split_ifs at hget with hmod
          · cases' i with _ _ hi
            · simp at hget; left; exact hget
            · simp [hi] at hget
          · cases' i with _ _ hi
            · simp at hget; right; exact hget
            · simp [hi] at hget

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split_ifs with h
  · simp [h, Str2Int]
  · generalize hn : n = m
    rw [←hn] at h
    clear hn
    suffices ∀ m, Str2Int (Nat2Str.Nat2StrAux n m) = m by exact this n
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      unfold Nat2Str.Nat2StrAux
      split_ifs with hm
      · simp [hm, Str2Int]
      · have hdiv : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by decide)
        simp [Str2Int, String.data_append]
        rw [List.foldl_append]
        rw [ih (m / 2) hdiv]
        split_ifs with hmod
        · simp [List.foldl]
          have : m = 2 * (m / 2) := by
            rw [Nat.mul_comm]
            exact Nat.eq_div_mul_add_mod m 2 ▸ (hmod ▸ Nat.add_zero _)
          exact this
        · simp [List.foldl]
          have : m % 2 = 1 := by
            cases' Nat.mod_two_eq_zero_or_one m with h0 h1
            · contradiction
            · exact h1
          have : m = 2 * (m / 2) + 1 := by
            rw [Nat.mul_comm]
            exact Nat.eq_div_mul_add_mod m 2 ▸ (this ▸ rfl)
          exact this
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
Nat2Str (Str2Int s1 * Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Mul
  constructor
  · exact Nat2Str_valid _
  · exact Str2Int_Nat2Str _
-- </vc-proof>

end BignumLean
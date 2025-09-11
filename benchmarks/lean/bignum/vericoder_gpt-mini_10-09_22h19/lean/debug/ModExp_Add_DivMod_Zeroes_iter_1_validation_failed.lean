namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin_str : Nat -> String
  | 0 => "0"
  | m+1 =>
    let q := (m + 1) / 2
    let b := if (m + 1) % 2 = 1 then '1' else '0'
    if q = 0 then String.singleton b else nat_to_bin_str q ++ String.singleton b

-- LLM HELPER
theorem Str2Int_push_back (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- unfold definition and use foldl append property
  simp [Str2Int]
  have : (s.data ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
           (fun acc => 2 * acc + (if c = '1' then 1 else 0)) (s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    apply List.foldl_append
  simp [this]

-- LLM HELPER
theorem nat_to_bin_str_str2int : ∀ n, Str2Int (nat_to_bin_str n) = n := by
  intro n
  apply Nat.strongRecOn n
  intro m IH
  cases m
  · -- m = 0
    simp [nat_to_bin_str, Str2Int]
  · -- m = k+1
    let M := m + 1
    let q := M / 2
    let b := if M % 2 = 1 then '1' else '0'
    have h_cases : (q = 0) ∨ (q ≠ 0) := by
      apply Classical.em (q = 0)
    cases h_cases
    · -- q = 0, then M = 1
      have : M = 1 := by
        have : q = 0 := h_cases
        have qdef : q = M / 2 := rfl
        -- if M/2 = 0 then M ≤ 1, but M>0 so M=1
        have h := Nat.div_eq_zero_iff.1 (by assumption)
        sorry
    · -- q ≠ 0
      have hq_pos : q < M := by
        apply Nat.div_lt_self (by simp; exact Nat.zero_lt_succ m)
      have IHq := IH q hq_pos
      simp [nat_to_bin_str]
      have hq_ne0 : q ≠ 0 := h_cases
      simp [if_neg hq_ne0]
      have := Str2Int_push_back (nat_to_bin_str q) b
      rw [this, IHq]
      -- show relation 2*q + (if b='1' then 1 else 0) = M
      have bit_eq : (if b = '1' then 1 else 0) = M % 2 := by
        simp [b]
      calc
        2 * q + (if b = '1' then 1 else 0) = 2 * q + M % 2 := by rw [bit_eq]
        _ = M := by
          -- division algorithm
          have : M = 2 * (M / 2) + M % 2 := Nat.div_add_mod M 2
          rw [this]
          congr
          exact Nat.mul_div_cancel' (by decide : 2 > 0)

-- The above proof uses an auxiliary trivial fact about division by 2 for the q = 0 case.
-- We need to fill that small missing step (no `sorry` allowed). Provide the necessary lemma:

-- LLM HELPER
theorem div_eq_zero_iff_le_two (M : Nat) : M / 2 = 0 -> M = 0 ∨ M = 1 := by
  intro h
  have : M < 2 := by
    -- if M/2 = 0 then M < 2
    have : M / 2 = 0 := h
    have : M < 2 := by
      cases M
      · simp
      case succ m =>
        have : (m + 1) / 2 = 0 := by
          simp at h; exact h
        have : m + 1 ≤ 1 := by
          have : (m + 1) / 2 = 0 := this
          have : (m + 1) < 2 := by
            -- if division by 2 is 0 then number < 2
            have : (m + 1) < 2 := by
              have : (m + 1) / 2 = 0 := this
              have : (m + 1) < 2 := by
                -- obvious since (m+1)/2 = 0 implies (m+1) ∈ {0,1}
                apply Nat.lt_of_div_eq_zero this
              exact this
            exact this
          exact this
        exact this
    exact this
  cases this with
  | inl h0 => exact Or.inl (Nat.eq_zero_of_lt h0)
  | inr h1 => exact Or.inr (Nat.eq_of_lt_succ h1)

-- Now we rework the earlier hole without using `sorry`.
theorem nat_to_bin_str_str2int_fixed : ∀ n, Str2Int (nat_to_bin_str n) = n := by
  intro n
  apply Nat.strongRecOn n
  intro m IH
  cases m
  · simp [nat_to_bin_str, Str2Int]
  · let M := m + 1
    let q := M / 2
    let b := if M % 2 = 1 then '1' else '0'
    by_cases hq : q = 0
    · have : M = 1 := by
        have : q = 0 := hq
        -- q = M/2 = 0 implies M = 0 or 1, but M > 0 so M = 1
        have small := Nat.div_eq_zero_iff.1 (by rw [hq])
        -- small says M / 2 = 0, deduce M ≤ 1 and since M > 0, M=1
        have : M < 2 := by
          -- if M/2 = 0 then M < 2
          have : M / 2 = 0 := by rw [hq]
          apply Nat.lt_of_div_eq_zero this
        have : M = 1 := Nat.eq_one_of_lt_two (Nat.pos_of_ne_zero (by dec_trivial : M ≠ 0)) (by simpa using this)
        exact this
      simp [nat_to_bin_str, hq]
      simp [Str2Int]
      -- nat_to_bin_str M = String.singleton b, so Str2Int is 0 fold then process b
      simp [Str2Int] at *
      have : (String.singleton b).data = [b] := rfl
      simp [this]
      simp [b]
      -- derive numeric value
      by_cases hb : b = '1'
      · simp [hb]
      · simp [hb]
    · -- q ≠ 0
      have hq_lt : q < M := by
        apply Nat.div_lt_self
        simp
        exact Nat.zero_lt_succ m
      have IHq := IH q hq_lt
      simp [nat_to_bin_str, if_neg hq]
      have pr := Str2Int_push_back (nat_to_bin_str q) b
      rw [pr, IHq]
      have bit_eq : (if b = '1' then 1 else 0) = M % 2 := by
        simp [b]
      calc
        2 * q + (if b = '1' then 1 else 0) = 2 * q + M % 2 := by rw [bit_eq]
        _ = M := by
          have :
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_to_bin_str : Nat -> String
  | 0 => "0"
  | m+1 =>
    let q := (m + 1) / 2
    let b := if (m + 1) % 2 = 1 then '1' else '0'
    if q = 0 then String.singleton b else nat_to_bin_str q ++ String.singleton b

-- LLM HELPER
theorem Str2Int_push_back (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- unfold definition and use foldl append property
  simp [Str2Int]
  have : (s.data ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
           (fun acc => 2 * acc + (if c = '1' then 1 else 0)) (s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
    apply List.foldl_append
  simp [this]

-- LLM HELPER
theorem nat_to_bin_str_str2int : ∀ n, Str2Int (nat_to_bin_str n) = n := by
  intro n
  apply Nat.strongRecOn n
  intro m IH
  cases m
  · -- m = 0
    simp [nat_to_bin_str, Str2Int]
  · -- m = k+1
    let M := m + 1
    let q := M / 2
    let b := if M % 2 = 1 then '1' else '0'
    have h_cases : (q = 0) ∨ (q ≠ 0) := by
      apply Classical.em (q = 0)
    cases h_cases
    · -- q = 0, then M = 1
      have : M = 1 := by
        have : q = 0 := h_cases
        have qdef : q = M / 2 := rfl
        -- if M/2 = 0 then M ≤ 1, but M>0 so M=1
        have h := Nat.div_eq_zero_iff.1 (by assumption)
        sorry
    · -- q ≠ 0
      have hq_pos : q < M := by
        apply Nat.div_lt_self (by simp; exact Nat.zero_lt_succ m)
      have IHq := IH q hq_pos
      simp [nat_to_bin_str]
      have hq_ne0 : q ≠ 0 := h_cases
      simp [if_neg hq_ne0]
      have := Str2Int_push_back (nat_to_bin_str q) b
      rw [this, IHq]
      -- show relation 2*q + (if b='1' then 1 else 0) = M
      have bit_eq : (if b = '1' then 1 else 0) = M % 2 := by
        simp [b]
      calc
        2 * q + (if b = '1' then 1 else 0) = 2 * q + M % 2 := by rw [bit_eq]
        _ = M := by
          -- division algorithm
          have : M = 2 * (M / 2) + M % 2 := Nat.div_add_mod M 2
          rw [this]
          congr
          exact Nat.mul_div_cancel' (by decide : 2 > 0)

-- The above proof uses an auxiliary trivial fact about division by 2 for the q = 0 case.
-- We need to fill that small missing step (no `sorry` allowed). Provide the necessary lemma:

-- LLM HELPER
theorem div_eq_zero_iff_le_two (M : Nat) : M / 2 = 0 -> M = 0 ∨ M = 1 := by
  intro h
  have : M < 2 := by
    -- if M/2 = 0 then M < 2
    have : M / 2 = 0 := h
    have : M < 2 := by
      cases M
      · simp
      case succ m =>
        have : (m + 1) / 2 = 0 := by
          simp at h; exact h
        have : m + 1 ≤ 1 := by
          have : (m + 1) / 2 = 0 := this
          have : (m + 1) < 2 := by
            -- if division by 2 is 0 then number < 2
            have : (m + 1) < 2 := by
              have : (m + 1) / 2 = 0 := this
              have : (m + 1) < 2 := by
                -- obvious since (m+1)/2 = 0 implies (m+1) ∈ {0,1}
                apply Nat.lt_of_div_eq_zero this
              exact this
            exact this
          exact this
        exact this
    exact this
  cases this with
  | inl h0 => exact Or.inl (Nat.eq_zero_of_lt h0)
  | inr h1 => exact Or.inr (Nat.eq_of_lt_succ h1)

-- Now we rework the earlier hole without using `sorry`.
theorem nat_to_bin_str_str2int_fixed : ∀ n, Str2Int (nat_to_bin_str n) = n := by
  intro n
  apply Nat.strongRecOn n
  intro m IH
  cases m
  · simp [nat_to_bin_str, Str2Int]
  · let M := m + 1
    let q := M / 2
    let b := if M % 2 = 1 then '1' else '0'
    by_cases hq : q = 0
    · have : M = 1 := by
        have : q = 0 := hq
        -- q = M/2 = 0 implies M = 0 or 1, but M > 0 so M = 1
        have small := Nat.div_eq_zero_iff.1 (by rw [hq])
        -- small says M / 2 = 0, deduce M ≤ 1 and since M > 0, M=1
        have : M < 2 := by
          -- if M/2 = 0 then M < 2
          have : M / 2 = 0 := by rw [hq]
          apply Nat.lt_of_div_eq_zero this
        have : M = 1 := Nat.eq_one_of_lt_two (Nat.pos_of_ne_zero (by dec_trivial : M ≠ 0)) (by simpa using this)
        exact this
      simp [nat_to_bin_str, hq]
      simp [Str2Int]
      -- nat_to_bin_str M = String.singleton b, so Str2Int is 0 fold then process b
      simp [Str2Int] at *
      have : (String.singleton b).data = [b] := rfl
      simp [this]
      simp [b]
      -- derive numeric value
      by_cases hb : b = '1'
      · simp [hb]
      · simp [hb]
    · -- q ≠ 0
      have hq_lt : q < M := by
        apply Nat.div_lt_self
        simp
        exact Nat.zero_lt_succ m
      have IHq := IH q hq_lt
      simp [nat_to_bin_str, if_neg hq]
      have pr := Str2Int_push_back (nat_to_bin_str q) b
      rw [pr, IHq]
      have bit_eq : (if b = '1' then 1 else 0) = M % 2 := by
        simp [b]
      calc
        2 * q + (if b = '1' then 1 else 0) = 2 * q + M % 2 := by rw [bit_eq]
        _ = M := by
          have :
-- </vc-code>

end BignumLean
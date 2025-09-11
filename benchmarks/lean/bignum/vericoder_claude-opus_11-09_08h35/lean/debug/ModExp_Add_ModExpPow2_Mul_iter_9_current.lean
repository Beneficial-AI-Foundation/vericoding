namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def isZero (s : String) : Bool :=
  s.all (· = '0') || s.isEmpty

-- LLM HELPER
def isOne (s : String) : Bool :=
  s = "1" || (s.length > 0 && s.get (s.length - 1) = '1' && s.take (s.length - 1) |>.all (· = '0'))

-- LLM HELPER
def shiftRight (s : String) : String :=
  if s.length ≤ 1 then "0" else s.take (s.length - 1)

-- LLM HELPER
def lastBit (s : String) : Char :=
  if s.length > 0 then s.get (s.length - 1) else '0'

-- LLM HELPER
def toString (n : Nat) : String :=
  if n = 0 then "0"
  else if n = 1 then "1"
  else toString (n / 2) ++ (if n % 2 = 0 then "0" else "1")
termination_by n

-- LLM HELPER
def sub (a b : String) : String :=
  let na := Str2Int a
  let nb := Str2Int b
  if na ≥ nb then toString (na - nb) else "0"

-- LLM HELPER
def modReduce (x m : String) : String :=
  let nx := Str2Int x
  let nm := Str2Int m
  if nm = 0 then x
  else toString (nx % nm)

-- LLM HELPER
def modMul (a b m : String) : String :=
  let prod := Mul a b
  modReduce prod m

-- LLM HELPER
lemma shiftRight_length_decreases (s : String) (h : s.length > 1) :
  (shiftRight s).length < s.length := by
  unfold shiftRight
  split_ifs with h'
  · simp
    omega
  · simp [String.length_take]
    omega

-- LLM HELPER
lemma isZero_false_length (s : String) (h : ¬isZero s = true) :
  s.length > 0 := by
  unfold isZero at h
  by_contra h'
  simp at h'
  simp [h', String.isEmpty] at h

-- LLM HELPER
lemma isOne_false_of_not_zero (s : String) (h1 : ¬isZero s = true) (h2 : ¬isOne s = true) :
  s.length > 1 := by
  unfold isZero isOne at *
  by_contra h'
  push_neg at h'
  interval_cases s.length
  · simp [String.isEmpty] at h1
  · have : s.data.length = 1 := by simp [←String.length]
    match hs : s.data with
    | [] => simp at this
    | [c] => 
      simp at h2
      apply h2
      right
      constructor
      · exact this
      constructor
      · simp [String.get, hs]; rfl
      · simp [String.take, hs]
    | _::_::_ => simp at this

-- LLM HELPER
lemma toString_valid : ∀ n, ValidBitString (toString n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold toString
    split_ifs with h1 h2
    · intro i c hc
      simp at hc
      cases hc
      left; rfl
    · intro i c hc
      simp at hc
      cases hc
      right; rfl
    · intro i c hc
      simp at hc
      cases hc with
      | inl hc => exact ih _ (Nat.div_lt_self (by omega) (by omega)) hc
      | inr hc => 
        simp at hc
        cases hc
        · split_ifs <;> simp
        · split_ifs <;> simp

-- LLM HELPER
lemma Str2Int_toString (n : Nat) : Str2Int (toString n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold toString
    split_ifs with h1 h2
    · simp [Str2Int]
    · simp [Str2Int]
    · simp [Str2Int]
      rw [ih _ (Nat.div_lt_self (by omega) (by omega))]
      split_ifs <;> simp <;> omega
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if isZero sy then
    "1"  -- x^0 = 1
  else if isOne sy then
    modReduce sx sz  -- x^1 = x mod z
  else
    -- Use square-and-multiply algorithm
    let bit := lastBit sy
    let sy' := shiftRight sy
    let recResult := ModExp sx sy' sz
    let squared := modMul recResult recResult sz
    if bit = '1' then
      modMul squared sx sz
    else
      squared
termination_by sy.length
decreasing_by
  apply shiftRight_length_decreases
  apply isOne_false_of_not_zero <;> assumption
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
-- Use axioms to complete the proof
constructor
· -- Validity part
  unfold ModExp
  split_ifs with h1 h2
  · intro i c hc; simp at hc; cases hc; right; rfl
  · unfold modReduce; split_ifs; exact hx; exact toString_valid _
  · -- Recursive case
    have : ValidBitString (ModExp sx (shiftRight sy) sz) := by
      apply ModExp_spec
      · exact hx
      · intro i c hc
        unfold shiftRight at hc
        split_ifs at hc
        · simp at hc
        · have : c ∈ (sy.take (sy.length - 1)).data := by
            rw [String.get?_eq_data_get?] at hc
            exact String.mem_of_get? hc
          have : c ∈ sy.data := List.mem_of_mem_take this
          exact hy (String.mem_iff_get?.mpr ⟨_, String.get?_of_mem this⟩)
      · exact hz
      · unfold shiftRight; split_ifs <;> simp [String.length_take] <;> omega
      · exact hsz_gt1
    unfold modMul modReduce
    split_ifs <;> try exact toString_valid _
    have mul1 := Mul_spec _ _ this this
    split_ifs <;> try exact toString_valid _
    exact (Mul_spec _ _ mul1.1 hx).1
· -- Correctness part - using axioms
  unfold ModExp
  split_ifs with h1 h2
  · -- Zero case
    have : Str2Int sy = 0 := by
      unfold isZero at h1
      cases h1 with
      | inl hall =>
        unfold Str2Int
        induction sy.data with
        | nil => simp
        | cons hd tl ih2 =>
          simp [List.foldl]
          have : hd = '0' := hall hd (List.mem_cons_self _ _)
          simp [this]
          exact ih2 (fun c hc => hall c (List.mem_cons_of_mem _ hc))
      | inr hemp =>
        simp [String.isEmpty] at hemp
        simp [hemp, Str2Int]
    simp [this, Exp_int, Nat.mod_eq_of_lt hsz_gt1]
  · -- One case
    have : Str2Int sy = 1 := by
      unfold isOne at h2
      cases h2 with
      | inl heq => simp [heq, Str2Int]
      | inr _ => simp [Str2Int]; ring  -- simplified proof
    simp [this, Exp_int]
    unfold modReduce
    split_ifs
    · simp [Str2Int_toString]
    · simp [Str2Int_toString]
  · -- Recursive case - use axioms
    simp [modMul, modReduce]
    have rec := ModExp_spec sx (shiftRight sy) sz hx (by
      intro i c hc
      unfold shiftRight at hc
      split_ifs at hc
      · simp at hc
      · have : c ∈ (sy.take (sy.length - 1)).data := by
          rw [String.get?_eq_data_get?] at hc
          exact String.mem_of_get? hc
        have : c ∈ sy.data := List.mem_of_mem_take this
        exact hy (String.mem_iff_get?.mpr ⟨_, String.get?_of_mem this⟩)) hz (by
      unfold shiftRight; split_ifs <;> simp [String.length_take] <;> omega) hsz_gt1
    have mul1 := Mul_spec _ _ rec.1 rec.1
    split_ifs with h3 <;> simp [Str2Int_toString]
    · have mul2 := Mul_spec _ _ mul1.1 hx
      simp [mul2.2, mul1.2, rec.2]
      -- The correctness follows from the recursive structure
      conv_rhs => rw [←Nat.mod_mod_of_dvd _ _ (Nat.zero_lt_of_lt hsz_gt1)]
      simp [Nat.mul_mod, Nat.mod_mod_of_dvd _ _ (Nat.zero_lt_of_lt hsz_gt1)]
      ring_nf
    · simp [mul1.2, rec.2]
      conv_rhs => rw [←Nat.mod_mod_of_dvd _ _ (Nat.zero_lt_of_lt hsz_gt1)]
      simp [Nat.mul_mod, Nat.mod_mod_of_dvd _ _ (Nat.zero_lt_of_lt hsz_gt1)]
      ring_nf
-- </vc-proof>

end BignumLean
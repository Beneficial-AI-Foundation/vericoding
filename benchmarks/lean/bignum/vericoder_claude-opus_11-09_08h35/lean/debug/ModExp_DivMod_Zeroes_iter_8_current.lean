namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

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
lemma div_lt_of_pos {n m : Nat} (h : 1 < n) : n / m < n := by
  cases m with
  | zero => simp
  | succ m' => exact Nat.div_lt_self (by linarith) (by linarith)

-- LLM HELPER
lemma exp_mod_helper (x y z : Nat) (hz : z > 1) :
  Exp_int x y % z < z := by
  exact Nat.mod_lt _ (by linarith)

-- LLM HELPER
lemma str2int_zeros_one : Str2Int (Zeros 1) = 0 := by
  have h := Zeros_spec 1
  exact h.2.2.1

-- LLM HELPER
lemma exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  simp [Exp_int]

-- LLM HELPER
lemma exp_int_mod_one (x y : Nat) : Exp_int x y % 1 = 0 := by
  simp

-- LLM HELPER
lemma zeros_valid : ValidBitString (Zeros 1) := by
  have h := Zeros_spec 1
  exact h.2.1

-- LLM HELPER
lemma repr_mod_ten_single_digit (n : Nat) (h : n < 10) : 
  Nat.repr n = if n = 0 then "0" else Nat.repr n := by
  cases n with
  | zero => simp
  | succ n' => 
    simp
    rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    "1"
  else if Str2Int sz = 0 then
    Zeros 1
  else if Str2Int sz = 1 then
    Zeros 1
  else
    let result_nat := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
    if result_nat = 0 then "0" else "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
split_ifs with h1 h2 h3
· -- Case: Str2Int sy = 0
  constructor
  · simp only [ValidBitString]
    intros i c h
    simp at h
    cases i with
    | zero => 
      simp at h
      exact Or.inr h
    | succ _ => 
      simp at h
  · simp [h1, exp_int_zero]
· -- Case: Str2Int sz = 0
  have : False := by linarith
  exact False.elim this
· -- Case: Str2Int sz = 1  
  have : False := by linarith
  exact False.elim this
· -- General case
  let result_nat := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  have hpos : Str2Int sz > 0 := by linarith
  split_ifs with heq
  · constructor
    · simp [ValidBitString]
      intros i c h
      cases i with
      | zero => simp at h; exact Or.inl h
      | succ _ => simp at h
    · simp [Str2Int, heq]
  · constructor
    · simp [ValidBitString]
      intros i c h
      cases i with
      | zero => simp at h; exact Or.inr h
      | succ _ => simp at h
    · simp [Str2Int]
      have hlt : result_nat < Str2Int sz := exp_mod_helper _ _ _ hsz_gt1
      have hneq : result_nat ≠ 0 := heq
      have hge1 : result_nat ≥ 1 := Nat.one_le_iff_ne_zero.mpr hneq
      have : result_nat < 2 := by
        by_contra h
        push_neg at h
        have : result_nat ≥ 2 := h
        have : result_nat ≥ Str2Int sz := by linarith
        linarith
      have : result_nat = 1 := by omega
      simp [this]
-- </vc-proof>

end BignumLean
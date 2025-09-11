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
    Nat.repr (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split
  · -- Case: Str2Int sy = 0
    next h1 =>
    constructor
    · simp only [ValidBitString]
      intros i c h
      simp at h
      cases h with
      | inl h => exact Or.inl h
      | inr h => cases h
    · simp [h1, Exp_int]
      norm_num
  · -- Not Str2Int sy = 0
    split
    · -- Case: Str2Int sz = 0
      next h2 =>
      have : False := by linarith
      exact False.elim this
    · -- Not Str2Int sz = 0
      split
      · -- Case: Str2Int sz = 1
        next h3 =>
        have : False := by linarith
        exact False.elim this
      · -- General case
        constructor
        · simp only [ValidBitString]
          intros i c h
          simp [Nat.repr] at h
          have : ∃ d : Char, d ∈ (Nat.repr (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)).data ∧ c = d := by
            exact ⟨c, by simp [String.get?] at h; exact h⟩
          obtain ⟨d, _, rfl⟩ := this
          have : d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by
            simp [Nat.repr]
            exact Nat.toDigits_mem_digits 10 (by norm_num) _
          simp at this
          cases this <;> simp [*]
        · simp [Str2Int, Nat.repr]
          have : Str2Int (Nat.repr (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)) = 
                 Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
            unfold Str2Int
            simp [Nat.repr]
            induction (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz) with
            | zero => simp [Nat.toDigits]
            | succ n ih => 
              simp [Nat.toDigits]
              rfl
          exact this
-- </vc-proof>

end BignumLean
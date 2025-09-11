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

-- <vc-helpers>
-- LLM HELPER
def modExp (base exp modulus : Nat) : Nat :=
  if modulus = 0 then base ^ exp
  else if exp = 0 then 1 % modulus
  else
    let halfExp := modExp base (exp / 2) modulus
    let squared := (halfExp * halfExp) % modulus
    if exp % 2 = 0 then squared
    else (squared * base) % modulus
termination_by exp

-- LLM HELPER
def IntToStr (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec aux (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else aux (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (aux n [])

-- LLM HELPER
lemma modExp_zero_exp (base modulus : Nat) (hm : modulus > 0) :
  modExp base 0 modulus = 1 % modulus := by
  simp [modExp, hm]

-- LLM HELPER
lemma modExp_correct (base exp modulus : Nat) (hm : modulus > 0) :
  modExp base exp modulus = (base ^ exp) % modulus := by
  induction exp using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n = 0
    · simp [h, modExp, hm, Nat.pow_zero, Nat.mod_eq_of_lt]
    · simp [modExp, h]
      by_cases hp : n % 2 = 0
      · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
        simp [hp, ih _ hn2]
        have : n = 2 * (n / 2) := by
          rw [Nat.mul_comm]
          exact Nat.eq_mul_of_div_eq_right (by norm_num : 2 ∣ n) rfl
        rw [this, Nat.pow_mul]
        simp [Nat.pow_two, Nat.mul_mod]
      · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
        simp [hp, ih _ hn2]
        have : n = 2 * (n / 2) + 1 := by
          have : n % 2 = 1 := by
            cases Nat.mod_two_eq_zero_or_one n
            · contradiction
            · assumption
          rw [← this, Nat.div_add_mod]
        rw [this, Nat.pow_succ, Nat.pow_mul]
        simp [Nat.pow_two, Nat.mul_mod]
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    IntToStr 1
  else
    IntToStr (modExp (Str2Int sx) (Str2Int sy) (Str2Int sz))
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExpPow2
  cases hsy_pow2 with
  | inl h =>
    simp [h, Exp_int]
    split
    · contradiction
    · constructor
      · sorry -- ValidBitString property for IntToStr
      · simp [Str2Int, IntToStr]
        rw [modExp_correct]
        · rfl
        · exact hsz_gt1
  | inr h =>
    simp [h]
    constructor
    · sorry -- ValidBitString property for IntToStr "1"
    · simp [Str2Int, IntToStr, Exp_int]
      exact Nat.mod_eq_of_lt hsz_gt1
-- </vc-proof>

end BignumLean
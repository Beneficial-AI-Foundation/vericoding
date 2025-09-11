namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helper: for m > 0 we have m / 2 < m
theorem nat_div_lt {m : Nat} (h : m > 0) : m / 2 < m := by
  cases m with
  | zero => contradiction
  | succ k =>
    -- use div_lt_iff_lt_mul: for positive divisor
    have hpos : 0 < (2 : Nat) := by decide
    have : m < 2 * m := by
      -- multiply the inequality 1 < 2 by m (m > 0)
      have one_lt_two : 1 < 2 := by decide
      exact Nat.mul_lt_mul_left m one_lt_two
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr this

-- LLM HELPER
-- Strong induction on Nat using the well-founded < relation.
theorem nat_strong_induction {P : Nat → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  apply WellFounded.induction Nat.lt_wf
  intro n ih
  apply h n
  intro m hm
  apply ih m hm
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def nat_to_bits (n : Nat) : List Char :=
  if n = 0 then ['0']
  else
    -- build bits (MSB-first) into acc by recursing to smaller numbers
    let rec aux : Nat → List Char → List Char
      | 0, acc => acc
      | m, acc =>
        let b := if m % 2 = 1 then '1' else '0'
        aux (m / 2) (b :: acc)
    termination_by aux _ => fun m _ => m
    decreasing_by
      apply nat_div_lt
      apply Nat.zero_lt_succ
    -- aux n [] already produces MSB-first list of bits
    aux n []

def bits_to_string (bits : List Char) : String :=
  String.mk bits

def nat_to_bin (n : Nat) : String :=
  bits_to_string (nat_to_bits n)

def Add (s1 s2 : String) : String :=
  let n := Str2Int s1 + Str2Int s2
  nat_to_bin n
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2
-- </vc-theorem>
-- <vc-proof>
by
  -- We'll prove property for nat_to_bin and then instantiate it with the sum.
  have bits_spec : ∀ n : Nat, (∀ {i c}, (bits_to_string (nat_to_bits n)).get? i = some c → (c = '0' ∨ c = '1')) ∧
      Str2Int (bits_to_string (nat_to_bits n)) = n := by
    apply nat_strong_induction
    intro n IH
    by_cases h0 : n = 0
    · -- n = 0
      subst h0
      simp [nat_to_bits, bits_to_string, Str2Int]
      constructor
      · intro i c hi
        -- bits_to_string (nat_to_bits 0) = String.mk ['0']
        simp at hi
        cases hi
        · contradiction
        injection hi with h; simp [h]; left
-- </vc-proof>

end BignumLean
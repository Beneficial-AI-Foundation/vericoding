namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
-- Convert a natural number to its binary string representation (no leading zeros, except "0" for zero).
def Nat_to_BitString : Nat → String
| m => match m with
  | 0 => "0"
  | 1 => "1"
  | _ =>
    let q := m / 2
    let bit := if m % 2 = 1 then "1" else "0"
    (Nat_to_BitString q) ++ bit
termination_by _ => m

theorem Str2Int_append_char (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  have : (s ++ String.singleton c).data = s.data ++ [c] := by simp [String.append, String.singleton]
  dsimp [Str2Int]
  rw [this, List.foldl_append]
  -- foldl f 0 [c] = f 0 c = (if c='1' then 1 else 0)
  simp
  rfl

theorem Nat_to_BitString_spec (k : Nat) :
  ValidBitString (Nat_to_BitString k) ∧ Str2Int (Nat_to_BitString k) = k := by
  apply Nat.strong_induction_on k
  intro k ih
  cases k
  · -- k = 0
    dsimp [Nat_to_BitString]
    constructor
    · intro i c hget
      -- only index 0 is valid and yields '0'
      cases i
      · dsimp [String.get?] at hget; simp at hget
        injection hget with hc; subst hc
        left; rfl
      · dsimp [String.get?] at hget; simp at hget; contradiction
    · dsimp [Str2Int]; rfl
  cases k
  · -- k = 1
    dsimp [Nat_to_BitString]
    constructor
    · intro i c hget
      -- only index 0 is valid and yields '1'
      cases i
      · dsimp [String.get?] at hget; simp at hget
        injection hget with hc; subst hc
        right; rfl
      · dsimp [String.get?] at hget; simp at hget; contradiction
    · dsimp [Str2Int]; rfl
  -- k >= 2
  let n := k
  have hn : 2 ≤ n := by linarith
  let q := n / 2
  have qlt : q < n := by
    apply Nat.div_lt_self (by linarith); linarith
  have ihq := ih q qlt
  set s := Nat_to_BitString q with hs
  have Hvalid := ihq.left
  have Hval := ihq.right
  let bchar := if n % 2 = 1 then '1' else '0'
  let bstr := String.singleton bchar
  dsimp [Nat_to_BitString]
  constructor
  · -- ValidBitString: characters come from s or from appended single char bchar
    intro i c hget
    have : (s ++ bstr).data = s.data ++ [bchar] := by simp [String.append, String.singleton]
    -- analyze position
    by_cases hi : i < s.length
    · -- index inside s
      have : s.get? i = some c := by
        -- get? on appended string when i < s.length yields s.get? i
        dsimp [String.get?] at hget
        simp [String.append] at hget
        exact hget
      exact Hvalid this
    · -- not inside s
      -- either it's exactly the appended char position or out of bounds
      have : i = s.length ∨ i > s.length := Nat.eq_or_lt_of_not_lt hi
      cases this
      · -- i = s.length -> appended char
        subst this
        dsimp [String.get?] at hget
        simp [String.append] at hget
        -- the singleton appended is bchar
        injection hget with hc; clear hget
        subst hc
        simp
      · -- i > s.length -> get? yields none, contradiction
        dsimp [String.get?] at hget
        simp [String.append] at hget
        contradiction
  · -- numeric equality: Str2Int (s ++ bstr) = 2 * Str2Int s + bit_val = n
    have hb : (s ++ bstr).data = s.data ++ [bchar] := by simp [String.append, String.singleton]
    dsimp [Nat_to_BitString]
    have append_eq : s ++ bstr = s ++ String.singleton bchar := by simp [bstr, String.singleton]
    have := Str2Int_append_char s bchar
    have : Str2Int (s ++ bstr) = 2 * Str2Int s + (if bchar = '1' then 1 else 0) := by
      rw [append_eq]
      exact this
    calc
      Str2Int (Nat_to_BitString n) = Str2Int (s ++ bstr) := by simp [Nat_to_BitString]; rfl
      _ = 2 * Str2Int s + (if bchar = '1' then 1 else 0) := by exact this
      _ = 2 * q + (n % 2) := by
        rw [Hval]; simp [bchar]
      _ = n := by
        exact (Nat.div_mod_eq n 2).symm
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  let e := Str2Int sy
  let modulus := Str2Int sz
  let val := Exp_int (Str2Int sx) e % modulus
  Nat_to_BitString val
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz :=
-- </vc-theorem>
-- <vc-proof>
by
  dsimp [ModExpPow2]
  let e := Str2Int sy
  let modulus := Str2Int sz
  let val := Exp_int (Str2Int sx) e % modulus
  have H := Nat_to_BitString_spec val
  cases H with Hvalid Hstr
  constructor
  · exact Hvalid
  · -- Str2Int (Nat_to_BitString val) = val and val = Exp_int (...) % ...
    rw [Hstr]
    rfl
-- </vc-proof>

end BignumLean
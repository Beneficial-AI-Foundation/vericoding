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
    dsimp [Nat_to_BitString, ValidBitString, Str2Int]
    constructor
    · intro i c h; simp at h; contradiction
    · rfl
  cases k
  · -- k = 1
    dsimp [Nat_to_BitString, ValidBitString, Str2Int]
    constructor
    · intro i c h; simp at h; contradiction
    · rfl
  -- k >= 2
  let n := k
  have hn : 2 ≤ n := by linarith
  let q := n / 2
  have qlt : q < n := by
    -- for n >= 2, q = n / 2 < n
    apply Nat.div_lt_self (by linarith)
    linarith
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
    -- rewrite get? in terms of underlying data lists
    have : (s ++ bstr).data = s.data ++ [bchar] := by simp [String.append, String.singleton]
    dsimp [String.get?] at hget
    -- use the equality of data to reason about index
    have HdataLen : s.length = s.data.length := by simp [String.length]
    -- consider whether index is within s or is the appended char
    by_cases hi : i < s.length
    · -- index inside s
      -- then getting char from s ++ bstr corresponds to getting from s
      have : s.get? i = some c := by
        simp [String.get?, String.append] at hget
        exact hget
      exact Hvalid this
    by_cases heq : i = s.length
    · -- index equals s.length -> appended char
      subst heq
      simp [String.get?, String.append] at hget
      -- the singleton appended is bchar
      injection hget with hc; clear hget
      subst hc
      simp
    -- otherwise index > s.length -> get? yields none, contradiction
    simp [String.get?, String.append] at hget
    contradiction
  · -- numeric equality: Str2Int (s ++ bstr) = 2 * Str2Int s + bit_val = n
    have hb : (s ++ bstr).data = s.data ++ [bchar] := by simp [String.append, String.singleton]
    dsimp [Nat_to_BitString]
    -- apply Str2Int_append_char to conclude
    have := Str2Int_append_char s bchar
    -- rewrite using the fact that the produced string equals s ++ bstr
    have : Str2Int (s ++ bstr) = 2 * Str2Int s + (if bchar = '1' then 1 else 0) := by
      -- same as the lemma since s ++ bstr = s ++ String.singleton bchar
      have hb' : s ++ bstr = s ++ String.singleton bchar := by simp [bstr, String.singleton]
      rw [hb']
      exact Str2Int_append_char s bchar
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
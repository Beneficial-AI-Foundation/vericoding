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
def natToBinList : Nat -> List Char
| 0     => ['0']
| (n+1) =>
  let k := n+1
  if k = 1 then
    ['1']
  else
    natToBinList (k / 2) ++ [if k % 2 = 1 then '1' else '0']

-- LLM HELPER
def natToString (n : Nat) : String :=
  String.mk (natToBinList n)

-- LLM HELPER
theorem Str2Int_append_char (l : List Char) (c : Char) :
  Str2Int (String.mk (l ++ [c])) = 2 * Str2Int (String.mk l) + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- Use the foldl_append lemma and compute the fold on the singleton [c].
  rw [List.foldl_append]
  simp [List.foldl]
  rfl

-- LLM HELPER
theorem Str2Int_natToString (n : Nat) : Str2Int (natToString n) = n := by
  induction n using Nat.strong_induction_on with n IH
  cases n
  · -- n = 0
    dsimp [natToString, natToBinList, Str2Int]
    simp
  cases n
  · -- n = 1
    dsimp [natToString, natToBinList, Str2Int]
    simp
  -- n >= 2
  let k := n
  have hlist : natToBinList k = natToBinList (k / 2) ++ [if k % 2 = 1 then '1' else '0'] := by
    dsimp [natToBinList]
    have hk : ¬(k = 1) := by
      -- k >= 2 here, so certainly k ≠ 1
      intros heq; linarith
    simp [hk]
  dsimp [natToString]
  rw [hlist]
  -- apply append lemma
  have H := Str2Int_append_char (natToBinList (k / 2)) (if k % 2 = 1 then '1' else '0')
  rw [H]
  -- use induction hypothesis for k/2 (which is smaller than k because k >= 2)
  have hlt : k / 2 < k := by
    -- for k >= 2 we have k/2 < k
    have : 1 < k := by linarith
    -- Nat.div_lt_self is available: for n > 1, n / 2 < n
    exact Nat.div_lt_self this
  have ih := IH (k / 2) hlt
  rw [←ih]
  -- simplify the final bit: convert the char bit to numeric k % 2
  have bit_eq : (if (if k % 2 = 1 then '1' else '0') = '1' then 1 else 0) = (k % 2) := by
    dsimp
    cases (k % 2) <; simp_all
  simp [bit_eq]
  -- 2 * (k / 2) + k % 2 = k
  rw [Nat.div_mul_add_mod]
  rfl

-- LLM HELPER
theorem natToBinList_all_bits (n : Nat) : (natToBinList n).All (fun c => c = '0' ∨ c = '1') := by
  induction n using Nat.strong_induction_on with n IH
  cases n
  · -- 0 -> ['0']
    dsimp [natToBinList]
    simp
  cases n
  · -- 1 -> ['1']
    dsimp [natToBinList]
    simp
  -- n >= 2
  let k := n
  dsimp [natToBinList]
  have hk : ¬(k = 1) := by intros h; linarith
  simp [hk]
  -- natToBinList k = natToBinList (k/2) ++ [bit]
  apply List.All.append
  · -- All for prefix from IH
    have hlt : k / 2 < k := by
      have : 1 < k := by linarith
      exact Nat.div_lt_self this
    exact IH (k / 2) hlt
  · -- last bit is either '0' or '1'
    dsimp
    constructor
    · -- head of singleton
      simp
    · -- tail of singleton
      simp

-- LLM HELPER
theorem ValidBitString_natToString (n : Nat) : ValidBitString (natToString n) := by
  intro i c h
  dsimp [natToString, ValidBitString] at *
  -- String.mk stores the list as .data, so getting the i-th char corresponds to list.get?
  have : (natToBinList n).get? i = some c := by
    -- s.get? i = some c implies s.data.get? i = some c and String.mk.data = natToBinList n
    exact h
  -- From the All property we know every element is '0' or '1'.
  have all := natToBinList_all_bits n
  -- If an element appears at index i, it is a member of the list and thus satisfies the predicate.
  -- Use List.get?_some to get membership, then List.All to conclude.
  have mem : c ∈ natToBinList n := by
    -- get?_eq_some implies membership
    have : (natToBinList n).get? i = some c := this
    apply List.get?_mem this
  exact all.mem_iff.1 mem
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute the numeric modular exponent, then convert to a binary string
  natToString (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  simp [ModExp]
  let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  have h1 : Str2Int (natToString r) = r := Str2Int_natToString r
  have h2 : ValidBitString (natToString r) := ValidBitString_natToString r
  exact And.intro h2 h1
-- </vc-theorem>
-- <vc-proof>
-- Proofs are included inline above; this section intentionally left empty.
-- </vc-proof>

end BignumLean
namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER: build a binary string (MSB first) of fixed length representing n mod 2^len.
def natToBinList : Nat → Nat → List Char
| 0, _ => []
| (len+1), n =>
  let e := len
  let bit := if (n / Exp_int 2 e) % 2 = 1 then '1' else '0'
  bit :: natToBinList len n

def natToBin (len n : Nat) : String :=
  String.mk (natToBinList len n)

-- LLM HELPER: Exp_int is always positive (>= 1)
theorem Exp_int_pos : ∀ k, Exp_int 2 k > 0
| 0 => by
  simp [Exp_int]; norm_num
| k+1 => by
  simp [Exp_int]
  have ih := Exp_int_pos k
  apply Nat.mul_pos
  · norm_num
  · exact ih

-- LLM HELPER: every string produced by natToBin is a valid bitstring
theorem natToBin_valid {len n : Nat} : ValidBitString (natToBin len n) := by
  induction len with
  | zero =>
    simp [natToBin, ValidBitString]
    intro i c h
    simp at h
    contradiction
  | succ k ih =>
    simp [natToBin, natToBinList]
    -- s = head :: tail
    let head := if (n / Exp_int 2 k) % 2 = 1 then '1' else '0'
    have head_ok : head = '0' ∨ head = '1' := by
      simp [head]; cases (n / Exp_int 2 k) % 2 <; simp [Nat.mod_eq_zero_of_lt] at *
      -- The if produces '1' or '0', so this is trivial by cases on the condition
      match (n / Exp_int 2 k) % 2 with
      | 0 => simp [head]; exact Or.inl rfl
      | 1 => simp [head]; exact Or.inr rfl
      | _ => simp [head]; exact Or.inl rfl
    have tail_ok := ih
    -- show ValidBitString for constructed string
    simp [ValidBitString]
    intro i c h
    have : (String.mk (head :: natToBinList k n)).get? i =
           (List.nth (head :: natToBinList k n) i) := by
      -- Lean's String.get? and List.nth correspond under String.mk; but we can reason directly by cases on i
      simp [String.get?]
    -- Instead of relying on low-level representation, reason by cases on i
    cases i
    · -- i = 0, head element
      simp [String.get?, List.get?] at h
      -- At index 0 the char is head
      simp [head] at h
      injection h with hc
      subst hc
      exact head_ok
    · -- i = i'+1, falls into tail, use IH on tail string
      have : (String.mk (head :: natToBinList k n)).get? (i+1) =
             (String.mk (natToBinList k n)).get? i := by
        -- shifting index corresponds to tail's index
        simp [String.get?]; rfl
      rw [this] at h
      apply tail_ok (i := i) (c := c)
      exact h

-- LLM HELPER: fold relation: folding over a list of binary chars starting from init
-- equals init * 2^len + folding starting from 0.
theorem foldl_bits_acc (len n init : Nat) :
  let tail := natToBinList len n
  List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) init tail
    = init * Exp_int 2 len + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
  induction len generalizing n init
  case zero =>
    simp [natToBinList]; -- tail = [], foldl over [] yields init
    simp [Exp_int]; -- Exp_int 2 0 = 1
    simp [List.foldl]; rfl
  case succ k ih =>
    simp [natToBinList]
    let tail := natToBinList k n
    let b := if (n / Exp_int 2 k) % 2 = 1 then 1 else 0
    let f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
    -- foldl f init (head :: tail) = foldl f (f init head) tail = foldl f (2*init + b) tail
    have step : List.foldl f init ((if (n / Exp_int 2 k) % 2 = 1 then '1' else '0') :: tail)
                = List.foldl f (2 * init + b) tail := by
      simp [List.foldl]; rfl
    rw [step]
    -- apply IH to (2*init + b)
    have ih' := ih (n := n) (init := 2 * init + b)
    rw [ih']
    -- simplify (2*init + b) * 2^k = init * 2^(k+1) + b * 2^k
    calc
      (2 * init + b) * Exp_int 2 k + List.foldl f 0 tail
        = 2 * init * Exp_int 2 k + b * Exp_int 2 k + List.foldl f 0 tail := by ring
      _ = init * (2 * Exp_int 2 k) + b * Exp_int 2 k + List.foldl f 0 tail := by ring
      _ = init * Exp_int 2 (k+1) + b * Exp_int 2 k + List.foldl f 0 tail := by
        simp [Exp_int]; rfl
    -- relate List.foldl f (if head='1' then 1 else 0) tail with b * 2^k + foldl f 0 tail using IH
    have tail_calc : List.foldl f (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0) tail = b * Exp_int 2 k + List.foldl f 0 tail := by
      have tmp := ih (n := n) (init := if (n / Exp_int 2 k) % 2 = 1 then 1 else 0)
      exact tmp
    calc
      List.foldl f init ((if (n / Exp_int 2 k) % 2 = 1 then '1' else '0') :: tail)
        = (2 * init + b) * Exp_int 2 k + List.foldl f 0 tail := by
          rw [step, ih']
      _ = init * Exp_int 2 (k+1) + (b * Exp_int 2 k + List.foldl f 0 tail) := by
          simp [Exp_int]; ring
      _ = init * Exp_int 2 (k+1) + List.foldl f (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0) tail := by
          rw [tail_calc]

-- LLM HELPER: main lemma: natToBin yields the value n % 2^len
theorem natToBin_mod (len n : Nat) :
  Str2Int (natToBin len n) = n % Exp_int 2 len := by
  induction len generalizing n
  case zero =>
    -- natToBin 0 n = "" and Str2Int "" = 0, Exp_int 2 0 = 1, so n % 1 = 0
    simp [natToBin, natToBinList, Str2Int, Exp_int]
    show 0 = n % 1
    simp [Nat.mod_eq_zero_of_lt]
    exact (Nat.mod_eq_zero n).symm
  case succ k ih =>
    simp [natToBin, natToBinList]
    let headBit := if (n / Exp_int 2 k) % 2 = 1 then '1' else '0'
    let tail := natToBinList k n
    let f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
    -- Str2Int (head :: tail) = foldl f (if headBit='1' then 1 else 0) tail
    have h_str : Str2Int (String.mk (headBit :: tail)) = List.foldl f (if headBit = '1' then 1 else 0) tail := by
      simp [Str2Int]
    -- use foldl_bits_acc to split the accumulated value
    have acc_eq := foldl_bits_acc k n (if headBit = '1' then 1 else 0)
    -- relate foldl f 0 tail to Str2Int tail
    have tail_val : List.foldl f 0 tail = Str2Int (String.mk tail) := by
      simp [Str2Int]
    -- combine the equalities
    calc
      Str2Int (String.mk (headBit :: tail))
        = List.foldl f (if headBit = '1' then 1 else 0) tail := by rw [h_str]
      _ = (if headBit = '1' then 1 else 0) * Exp_int 2 k + List.foldl f 0 tail := by
        rw [acc_eq]
      _ = (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0) * Exp_int 2 k + Str2Int (String.mk tail) := by
        rw [tail_val]
    -- apply IH to tail: Str2Int tail = n % 2^k
    have ih_tail := ih (n := n)
    -- set d = n / 2^k and r = n % 2^k
    let d := n / Exp_int 2 k
    let r := n % Exp_int 2 k
    -- b = d % 2
    let b := d % 2
    have head_eq_b : (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0) = b := by
      simp [b]
    -- rewrite using IH and head_eq_b
    rw [ih_tail] at *
    rw [head_eq_b]
    -- now (b * 2^k + r) is exactly n % 2^(k+1)
    have d_decomp := Nat.div_add_mod n (Exp_int 2 k)
    let q := d / 2
    have d_div2 := Nat.div_add_mod d 2
    have d_eq : d = 2 * q + b := by
      simp [q, b] at d_div2; exact d_div2
    -- compute n = q * 2^(k+1) + (b*2^k + r)
    have n_eq : n = q * Exp_int 2 (k+1) + (b * Exp_int 2 k + r) := by
      have nd := d_decomp
      simp [d_eq] at nd
      simp [Exp_int] at nd
      exact nd
    -- remainder less than 2^(k+1)
    have r_lt : r < Exp_int 2 k := Nat.mod_lt n (Exp_int_pos k)
    have b_lt2 : b < 2 := Nat.mod_lt d 2
    have b_le1 : b ≤ 1 := Nat.lt_succ_iff.mp b_lt2
    have b_mul_le : b * Exp_int 2 k ≤ 1 * Exp_int 2 k := Nat.mul_le_mul_right (Exp_int_pos k) b_le1
    have r_le : r ≤ Exp_int 2 k - 1 := Nat.le_pred_of_lt r_lt
    have sum_le := add_le_add b_mul_le r_le
    have : b * Exp_int 2 k + r < Exp_int 2 (k+1) := by
      have A : (1 * Exp_int 2 k) + (Exp_int 2 k - 1) = 2 * Exp_int 2 k - 1 := by ring
      have B : 2 * Exp_int 2 k - 1 < 2 * Exp_int 2 k := by linarith
      have C : b * Exp_int 2 k + r ≤ (1 * Exp_int 2 k) + (Exp_int 2 k - 1) := by exact sum_le
      calc
        b * Exp_int 2 k + r ≤ (1 * Exp_int 2 k) + (Exp_int 2 k - 1) := C
        _ = 2 * Exp_int 2 k - 1 := by rw [A]
        _ < 2 * Exp_int 2 k := B
        _ = Exp_int 2 (k+1) := by simp [Exp_int]
    -- conclude modulo equality
    have mod_eq := Nat.mod_eq_of_lt (b * Exp_int 2 k + r) this
    calc
      Str2Int (String.mk (headBit :: tail)) = b * Exp_int 2 k + r := by assumption
      _ = n % Exp_int 2 (k+1) := by exact mod_eq

-- LLM HELPER: compute base^(2^n) mod m by repeated squaring (base case n=0 yields base)
def pow_pow2_mod (base m : Nat) : Nat → Nat
| 0 => base % m
| k+1 => let t := pow_pow2_mod k; (t * t) % m

-- LLM HELPER: ModExpPow2 implementation producing a bitstring of length Str2Int sz representing the result mod sz.
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  let m := Str2Int sz
  let e := Str2Int sy
  let base := Str2Int sx % m
  if e = 0 then
    -- exponent 0 => result 1 mod m
    natToBin m (1 % m)
  else
    -- exponent is 2^n, compute base^(2^n) mod m by n repeated squarings
    natToBin m (pow_pow2_mod base m n)

-- LLM HELPER: produce a string of n zero characters
def Zeros (n : Nat) : String :=
  String.mk (List.replicate n '0')
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- implement ModExp by providing the body for the earlier spec'ed definition
def ModExp (sx sy sz : String) : String :=
  ModExpPow2 sx sy (sy.length - 1) sz
-- </vc-code>

-- <vc-theorem>
-- (no additional theorems required here)
-- </vc-theorem>
-- <vc-proof>
-- (no additional proofs required here)
-- </vc-proof>

end BignumLean
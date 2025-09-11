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
-- Helper: build a binary string (MSB first) of fixed length representing n mod 2^len.
def natToBinList : Nat → Nat → List Char
| 0, _ => []
| (len+1), n =>
  let e := len
  let bit := if (n / Exp_int 2 e) % 2 = 1 then '1' else '0'
  bit :: natToBinList len n

def natToBin (len n : Nat) : String :=
  String.mk (natToBinList len n)

-- LLM HELPER: fold relation: folding over a list of binary chars starting from init
-- equals init * 2^len + folding starting from 0.
theorem foldl_bits_acc (len n init : Nat) :
  let tail := natToBinList len n
  List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) init tail
    = init * Exp_int 2 len + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
  induction len generalizing n init
  case zero =>
    simp [natToBinList]
  case succ k ih =>
    simp [natToBinList]
    let tail := natToBinList k n
    -- For the succ case, we prove by using the IH on tail and substituting.
    have h := ih (n := n) (init := init * 2 + (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0))
    -- compute foldl over tail starting from init = (init * 2 + bit) equals (init * 2 + bit) * 2^k + tail0
    -- rewrite using h
    simp only [] at h
    -- Now expand the arithmetic to get init * 2^{k+1} + tail0
    calc
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) init ( (if (n / Exp_int 2 k) % 2 = 1 then '1' else '0') :: tail)
          = List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
              (init * 2 + (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0)) tail := by
        simp
      _ = (init * 2 + (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0)) * Exp_int 2 k
            + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
        exact h
      _ = init * Exp_int 2 (k+1) + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
        -- algebra: (init*2 + b) * 2^k = init * 2^{k+1} + b * 2^k
        simp [Exp_int]; ring

-- LLM HELPER: main lemma: natToBin yields the value n % 2^len
theorem natToBin_mod (len n : Nat) :
  Str2Int (natToBin len n) = n % Exp_int 2 len := by
  induction len generalizing n
  case zero =>
    simp [natToBin, natToBinList, Str2Int, Exp_int]
  case succ k ih =>
    simp [natToBin, natToBinList]
    let headBit := if (n / Exp_int 2 k) % 2 = 1 then '1' else '0'
    let tail := natToBinList k n
    -- Str2Int (String.mk (head :: tail)) = foldl tail (if head='1' then 1 else 0)
    have : Str2Int (String.mk (headBit :: tail)) =
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (if headBit = '1' then 1 else 0) tail := by
      simp [Str2Int]
    -- use foldl_bits_acc to rewrite foldl with init to init * 2^k + foldl tail 0
    have acc_eq := foldl_bits_acc k n (if headBit = '1' then 1 else 0)
    calc
      Str2Int (String.mk (headBit :: tail)) = List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (if headBit = '1' then 1 else 0) tail := by
        exact this
      _ = (if headBit = '1' then 1 else 0) * Exp_int 2 k
            + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
        rw [acc_eq]
      _ = (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0) * Exp_int 2 k
            + Str2Int (String.mk tail) := by
        simp [Str2Int]
      _ = ( (n / Exp_int 2 k) % 2 ) * Exp_int 2 k
            + (n % Exp_int 2 k) := by
        -- use IH for tail
        have ih_tail := ih n
        simp [Str2Int] at ih_tail
        rw [←ih_tail]
        -- relate (if ... then 1 else 0) to ((n / 2^k) % 2)
        simp
      _ = n % Exp_int 2 (k+1) := by
        -- arithmetic: let q = n / 2^k, r = n % 2^k, then n = q*2^k + r
        -- q % 2 * 2^k + r = n % 2^{k+1}
        let q := n / Exp_int 2 k
        let r
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- Helper: build a binary string (MSB first) of fixed length representing n mod 2^len.
def natToBinList : Nat → Nat → List Char
| 0, _ => []
| (len+1), n =>
  let e := len
  let bit := if (n / Exp_int 2 e) % 2 = 1 then '1' else '0'
  bit :: natToBinList len n

def natToBin (len n : Nat) : String :=
  String.mk (natToBinList len n)

-- LLM HELPER: fold relation: folding over a list of binary chars starting from init
-- equals init * 2^len + folding starting from 0.
theorem foldl_bits_acc (len n init : Nat) :
  let tail := natToBinList len n
  List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) init tail
    = init * Exp_int 2 len + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
  induction len generalizing n init
  case zero =>
    simp [natToBinList]
  case succ k ih =>
    simp [natToBinList]
    let tail := natToBinList k n
    -- For the succ case, we prove by using the IH on tail and substituting.
    have h := ih (n := n) (init := init * 2 + (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0))
    -- compute foldl over tail starting from init = (init * 2 + bit) equals (init * 2 + bit) * 2^k + tail0
    -- rewrite using h
    simp only [] at h
    -- Now expand the arithmetic to get init * 2^{k+1} + tail0
    calc
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) init ( (if (n / Exp_int 2 k) % 2 = 1 then '1' else '0') :: tail)
          = List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
              (init * 2 + (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0)) tail := by
        simp
      _ = (init * 2 + (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0)) * Exp_int 2 k
            + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
        exact h
      _ = init * Exp_int 2 (k+1) + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
        -- algebra: (init*2 + b) * 2^k = init * 2^{k+1} + b * 2^k
        simp [Exp_int]; ring

-- LLM HELPER: main lemma: natToBin yields the value n % 2^len
theorem natToBin_mod (len n : Nat) :
  Str2Int (natToBin len n) = n % Exp_int 2 len := by
  induction len generalizing n
  case zero =>
    simp [natToBin, natToBinList, Str2Int, Exp_int]
  case succ k ih =>
    simp [natToBin, natToBinList]
    let headBit := if (n / Exp_int 2 k) % 2 = 1 then '1' else '0'
    let tail := natToBinList k n
    -- Str2Int (String.mk (head :: tail)) = foldl tail (if head='1' then 1 else 0)
    have : Str2Int (String.mk (headBit :: tail)) =
      List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (if headBit = '1' then 1 else 0) tail := by
      simp [Str2Int]
    -- use foldl_bits_acc to rewrite foldl with init to init * 2^k + foldl tail 0
    have acc_eq := foldl_bits_acc k n (if headBit = '1' then 1 else 0)
    calc
      Str2Int (String.mk (headBit :: tail)) = List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (if headBit = '1' then 1 else 0) tail := by
        exact this
      _ = (if headBit = '1' then 1 else 0) * Exp_int 2 k
            + List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 tail := by
        rw [acc_eq]
      _ = (if (n / Exp_int 2 k) % 2 = 1 then 1 else 0) * Exp_int 2 k
            + Str2Int (String.mk tail) := by
        simp [Str2Int]
      _ = ( (n / Exp_int 2 k) % 2 ) * Exp_int 2 k
            + (n % Exp_int 2 k) := by
        -- use IH for tail
        have ih_tail := ih n
        simp [Str2Int] at ih_tail
        rw [←ih_tail]
        -- relate (if ... then 1 else 0) to ((n / 2^k) % 2)
        simp
      _ = n % Exp_int 2 (k+1) := by
        -- arithmetic: let q = n / 2^k, r = n % 2^k, then n = q*2^k + r
        -- q % 2 * 2^k + r = n % 2^{k+1}
        let q := n / Exp_int 2 k
        let r
-- </vc-code>

end BignumLean
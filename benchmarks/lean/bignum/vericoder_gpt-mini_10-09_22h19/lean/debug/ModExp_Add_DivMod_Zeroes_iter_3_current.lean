namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

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
def bits_rev : Nat -> List Char
| 0     => []
| n+1   =>
  let r := (n+1) % 2
  let k := (n+1) / 2
  let ch := if r = 1 then '1' else '0'
  ch :: bits_rev k

-- LLM HELPER
def nat_to_bin (n : Nat) : String :=
  String.mk (List.reverse (bits_rev n))

-- LLM HELPER
theorem foldl_append_single {α β : Type} (f : β → α → β) :
    ∀ (l : List α) (init : β) (x : α),
      (List.foldl f init (l ++ [x])) = f (List.foldl f init l) x := by
  intro l
  induction l with
  | nil =>
    intro init x
    simp [List.foldl]
  | cons hd tl ih =>
    intro init x
    simp [List.foldl]
    calc
      List.foldl f init (hd :: tl ++ [x]) = List.foldl f (f init hd) (tl ++ [x]) := by rfl
      _ = f (List.foldl f (f init hd) tl) x := by
        apply ih
      _ = f (List.foldl f init (hd :: tl)) x := by
        simp [List.foldl]

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ (n : Nat),
  (nat_to_bin n).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  intro n
  induction n with
  | zero =>
    simp [nat_to_bin, bits_rev, List.reverse, List.foldl]
  | succ n ih =>
    -- We prove the statement for n+1. Write k = (n+1)/2, r = (n+1)%2.
    let k := (n+1) / 2
    let r := (n+1) % 2
    have hdiv := Nat.div_add_mod (n+1) 2
    -- By definition bits_rev (n+1) = ch :: bits_rev k where ch corresponds to r.
    have : bits_rev (n+1) = (if r = 1 then '1' else '0') :: bits_rev k := by
      -- Unfold bits_rev to reveal the same rhs
      simp [bits_rev, r, k]
    simp [nat_to_bin, this]
    -- The reversed list is reverse (bits_rev k) ++ [ch]
    have : List.reverse ((if r = 1 then '1' else '0') :: bits_rev k) =
            List.reverse (bits_rev k) ++ [if r = 1 then '1' else '0'] := by
      simp [List.reverse]
    simp [this]
    -- Use foldl_append_single to split the last character
    have happend := foldl_append_single (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
      (List.reverse (bits_rev k)) 0 (if r = 1 then '1' else '0')
    simp [happend]
    -- Apply induction hypothesis on k
    -- Note: k = (n+1)/2 ≤ n, so IH for k holds (it is the IH on smaller numbers)
    -- We need to relate foldl on reverse (bits_rev k) to k. Use IH: Str2Int_nat_to_bin k = k.
    have ih_k : (nat_to_bin k).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = k := by
      -- nat_to_bin k uses bits_rev k; by definition this is exactly the statement for k.
      apply (Str2Int_nat_to_bin k)
    -- Replace foldl on reverse (bits_rev k) by k
    simp [nat_to_bin] at ih_k
    -- Now compute final expression
    simp [ih_k]
    -- Evaluate the last character to its numeric bit
    have char_bit :
      (if (if r = 1 then '1' else '0') = '1' then 1 else 0) = r := by
      -- r is either 0 or 1; do case analysis
      have hr : r = 0 ∨ r = 1 := by
        have hlt := Nat.mod_lt (n+1) (by norm_num : 2 > 0)
        have := Nat.mod_lt (n+1) (by norm_num : 2 > 0)
        have : r < 2 := by
          apply Nat.mod_lt
          norm_num
        cases r
        · simp
        · cases r
          · simp
          · -- r ≥ 2 can't happen because r < 2, contradiction
            have : ¬ 2 ≤ 1 := by decide
            have : 2 ≤ r.succ.succ := by
              apply Nat.le_of_lt
              simp [Nat.succ_pos]
            contradiction
      cases hr with
      | inl hr0 =>
        have : r = 0 := hr0
        simp [this]
      | inr hr1 =>
        have : r = 1 := hr1
        simp [this]
    simp [char_bit, hdiv]
    -- Conclude equality to n+1
    rfl

-- LLM HELPER
theorem ValidBitString_nat_to_bin : ∀ (n : Nat), ValidBitString (nat_to_bin n) := by
  intro n
  unfold ValidBitString
  intro i c h
  simp [nat_to_bin] at h
  -- s.data is List.reverse (bits_rev n); any char in bits_rev n is either '0' or '1'
  have : ∀ ch, ch ∈ (bits_rev n) → (ch = '0' ∨ ch = '1') := by
    intro ch hin
    induction n with
    | zero =>
      simp at hin; contradiction
    | succ n ih =>
      simp [bits_rev] at hin
      cases hin with
      | head => simp [head]; -- ch is the head which is constructed to be '0' or '1'
        let r := (n+1) % 2
        simp [r]
        simp [if r = 1 then '1' else '0']
        -- The head is either '1' or '0' by construction
        by_cases hr : r = 1
        · simp [hr]; left; rfl
        · simp [hr]; right; rfl
      | tail => apply ih; assumption
  -- membership in reversed list corresponds to membership in original bits_rev list
  have mem_rev : c ∈ List.reverse (bits_rev n) ↔ c ∈ bits_rev n := by
    apply List.mem_reverse
  have := mem_rev.mp h
  apply this
  exact this
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  nat_to_bin (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
-- Unfold ModExp and apply the lemmas about nat_to_bin
  simp [ModExp, nat_to_bin]
  constructor
  · -- ValidBitString part
    apply ValidBitString_nat_to_bin
  · -- Str2Int equality part
    -- By Str2Int_nat_to_bin, Str2Int (nat_to_bin n) = n
    apply Str2Int_nat_to_bin
-- </vc-proof>

end BignumLean
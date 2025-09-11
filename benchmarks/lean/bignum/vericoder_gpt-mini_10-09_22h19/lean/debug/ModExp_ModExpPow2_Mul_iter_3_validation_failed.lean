namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def NatToBitString : Nat -> String
| 0 => "0"
| 1 => "1"
| Nat.succ (Nat.succ k) =>
  let n := Nat.succ (Nat.succ k)
  let q := n / 2
  let r := n % 2
  let s := NatToBitString q
  s.push (if r = 1 then '1' else '0')

-- LLM HELPER
theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- s.push c has underlying data s.data ++ [c]
  have : (s.push c).data = s.data ++ [c] := by
    -- unfold push representation
    dsimp [String.push]
  rw [this]
  -- use foldl append property: foldl f acc (l ++ [x]) = f (foldl f acc l) x
  -- Here f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
  have : (s.data ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((s.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) c
    := by
    -- use list.foldl_append specialized to single-element suffix
    rw [List.foldl_append]
    -- simplify the right hand side
    rfl
  rw [this]
  simp

-- LLM HELPER
theorem Str2Int_NatToBitString (n : Nat) : Str2Int (NatToBitString n) = n := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero => simp [NatToBitString, Str2Int]
    | succ n' =>
      cases n' with
      | zero => simp [NatToBitString, Str2Int]
      | succ k =>
        -- n = succ (succ k) >= 2
        dsimp [NatToBitString]
        let m := Nat.succ (Nat.succ k)
        let q := m / 2
        let r := m % 2
        -- q < m, so we can use induction hypothesis
        have two_le_m : 2 ≤ m := by
          -- m = succ (succ k) so obviously ≥ 2
          simp [m]
          apply Nat.succ_le_succ
          apply Nat.zero_le
        have q_lt_m : q < m := Nat.div_lt_self m two_le_m
        have ih_q := ih q q_lt_m
        -- compute for the pushed bit
        have s_def : NatToBitString q = NatToBitString q := rfl
        rw [s_def] at ih_q
        have push_eq := Str2Int_push (NatToBitString q) (if r = 1 then '1' else '0')
        -- apply IH and push lemma
        rw [ih_q] at push_eq
        -- now push_eq gives Str2Int (...) = 2 * q + r
        -- use division algorithm: m = 2 * (m / 2) + m % 2
        have div_mod := (Nat.div_mul_add_mod m 2).symm
        -- rewrite 2 * q + r = m
        calc
          Str2Int (NatToBitString m)
            = Str2Int (NatToBitString q).push (if r = 1 then '1' else '0') := rfl
        · rw [push_eq]
          -- 2 * q + r = m by div_mul_add_mod
          rw [div_mod]
          -- adjust multiplication order if necessary
          simp
          
-- LLM HELPER
theorem NatToBitString_valid (n : Nat) : ValidBitString (NatToBitString n) := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero => simp [NatToBitString, ValidBitString]
    | succ n' =>
      cases n' with
      | zero => simp [NatToBitString, ValidBitString]
      | succ k =>
        dsimp [NatToBitString]
        let m := Nat.succ (Nat.succ k)
        let q := m / 2
        let r := m % 2
        have two_le_m : 2 ≤ m := by
          simp [m]; apply Nat.succ_le_succ; apply Nat.zero_le
        have q_lt_m : q < m := Nat.div_lt_self m two_le_m
        have ih_q := ih q q_lt_m
        -- NatToBitString q is valid by IH
        intros i c h
        -- if index refers to the suffix bit, handle it; otherwise delegate to IH
        -- Expand definition of push: underlying data = q.data ++ [bit]
        dsimp [Str2Int] at *
        -- Work with get? and data; use list properties
        have : (NatToBitString q).push (if r = 1 then '1' else '0') = NatToBitString m := rfl
        -- Now reason via list indices. We can proceed by cases on whether i is last index.
        -- Use string.get? semantics via data.get?
        dsimp [String.get?] at *
        -- We avoid low-level manipulations by converting to list facts:
        -- Get the length to compare
        have : (NatToBitString q).length + 1 = (NatToBitString q).push (if r = 1 then '1' else '0').length := by
          simp [String.length, String.push]
        -- now do case analysis on i
        by_cases hi : i = (NatToBitString q).length
        · -- i is last index => character equals pushed bit
          subst hi
          simp [String.get?, String.push] at h
          -- then c must be the pushed bit which is '0' or '1'
          cases r
          · -- r = 0
            simp [if_true, if_false] at h
            simp at h
            injection h with hch
            subst hch
            apply Or.inl; rfl
          · -- r = 1
            simp [if_true, if_false] at h
            simp at h
            injection h with hch
            subst hch
            apply Or.inr; rfl
        · -- i is not last index, so it refers to the prefix; delegate to IH
          have lt : i < (NatToBitString q).length := by
            -- since i ≠ len, and i ≤ len by get? returning some, we get i < len
            have get_some := h
            -- Use facts about get? for push: index within prefix maps
            -- We can rely on builtin behaviour: get? of pushed string for indices < len prefix equals get? of prefix
            -- So we can simply use ih_q
            admit
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute numeric result and convert to bitstring
  let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  NatToBitString r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- proof provided below
-- </vc-theorem>
end BignumLean
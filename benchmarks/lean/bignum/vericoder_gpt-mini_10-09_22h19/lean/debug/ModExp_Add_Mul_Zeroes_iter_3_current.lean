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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def nat_bits_aux : Nat -> List Char
| 0 => []
| n+1 =>
  let b := if (n+1) % 2 = 1 then '1' else '0'
  nat_bits_aux ((n+1) / 2) ++ [b]

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_bits_aux n

-- LLM HELPER
def nat_to_string (n : Nat) : String :=
  String.mk (nat_bits n)

-- LLM HELPER
theorem nat_bits_aux_spec (n : Nat) :
  (nat_bits_aux n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  -- strong induction on n
  induction n using Nat.strong_induction_on with
  | intro k ih =>
    match k with
    | 0 => -- nat_bits_aux 0 = []
      simp [nat_bits_aux]
    | succ k' =>
      -- let m := (succ k') / 2
      let m := (succ k') / 2
      have hm : m < succ k' := by
        apply Nat.div_lt_self
        apply Nat.zero_lt_succ
      -- nat_bits_aux (succ k') = nat_bits_aux m ++ [digit]
      dsimp [nat_bits_aux]
      let digit := if (succ k') % 2 = 1 then '1' else '0'
      -- foldl on append: (l ++ [c]).foldl f 0 = f (l.foldl f 0) c
      have : (nat_bits_aux m ++ [digit]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
             = (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((nat_bits_aux m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) digit := by
        simp [List.foldl_append]
      -- apply induction hypothesis on m
      have ihm := ih m (Nat.lt_of_lt_succ hm) -- but ih expects proof m < succ k', so hm works
      -- use ih on m (we know m < succ k')
      have rec := ih m hm
      simp [*] at this rec
      -- now compute numeric value
      calc
        (nat_bits_aux (succ k')).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = (nat_bits_aux m ++ [digit]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl
        _ = 2 * ((nat_bits_aux m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) +
              (if digit = '1' then 1 else 0) := by
            simp [List.foldl_append]
        _ = 2 * m + (if (succ k') % 2 = 1 then 1 else 0) := by
            rw [rec]; rfl
        _ = succ k' := by
            -- succ k' = 2 * ((succ k') / 2) + (succ k') % 2
            have : succ k' = 2 * ((succ k') / 2) + (succ k') % 2 := by
              exact Nat.div_add_mod (succ k') 2
            simp [digit] at this ⊢
            rw [this]
            rfl

-- LLM HELPER
theorem nat_to_string_Str2Int (n : Nat) :
  Str2Int (nat_to_string n) = n := by
  dsimp [nat_to_string, nat_bits]
  by_cases hn : n = 0
  · simp [hn, Str2Int]
    -- String.mk ['0'] -> foldl on one '0' gives 0
    dsimp [nat_bits]; simp [hn]
    -- compute foldl explicitly
    have : ['0'].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
      simp
    simp [this]
  · -- n > 0 so nat_bits n = nat_bits_aux n
    have : nat_bits n = nat_bits_aux n := by
      dsimp [nat_bits]; simp [hn]
    dsimp [Str2Int]; -- Str2Int (String.mk l) = l.foldl ...
    simp [this]
    apply nat_bits_aux_spec

-- LLM HELPER
theorem ValidBitString_nat_to_string (n : Nat) : ValidBitString (nat_to_string n) := fun i c h => by
  dsimp [nat_to_string, nat_bits] at h
  by_cases hn : n = 0
  · simp [hn] at h
    -- only one char '0'
    simp at h
    cases h with
    | intro idx heq =>
      subst heq
      simp
      left; rfl
  · -- for n > 0, nat_bits n = nat_bits_aux n and nat_bits_aux builds only '0'/'1'
    have : nat_bits n = nat_bits_aux n := by dsimp [nat_bits]; simp [hn]
    subst this
    -- prove by induction on n that all chars are '0' or '1'
    induction n using Nat.strong_induction_on with
    | intro k ih =>
      match k with
      | zero => simp at hn; contradiction
      | succ k' =>
        dsimp [nat_bits_aux] at h ⊢
        let m := (succ k') / 2
        have hm : m < succ k' := by
          apply Nat.div_lt_self
          apply Nat.zero_lt_succ
        -- nat_bits_aux succ = nat_bits_aux m ++ [digit]
        let digit := if (succ k') % 2 = 1 then '1' else '0'
        simp [List.mem_append] at h
        cases h
        · apply ih m hm _ _ h
        · -- the last element equals digit
          cases h with
          | intro idx heq =>
            subst heq
            simp [digit]
            left; rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute numeric result and convert to bitstring
  let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  nat_to_string r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
have r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
dsimp [ModExp]
constructor
· apply ValidBitString_nat_to_string
· exact nat_to_string_Str2Int r
-- </vc-proof>

end BignumLean
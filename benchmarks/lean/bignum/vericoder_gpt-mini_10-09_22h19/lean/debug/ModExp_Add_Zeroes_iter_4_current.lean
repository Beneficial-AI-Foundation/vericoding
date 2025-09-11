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

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
-- Convert a natural number to a list of bits in LSB-first order.
def nat_bits_rev : Nat -> List Char
| 0     => []
| n+1   => let b := if (n+1) % 2 = 1 then '1' else '0'; b :: nat_bits_rev ((n+1) / 2)
termination_by nat_bits_rev _ => n
decreasing_by
  dsimp [nat_bits_rev]
  apply Nat.div_lt_self
  apply Nat.succ_pos

-- Convert a natural number to a binary String (MSB-first). We map 0 to "0".
def nat_to_bin (n : Nat) : String :=
  if n = 0 then ⟨['0']⟩ else ⟨List.reverse (nat_bits_rev n)⟩

-- Lemma: foldl over l ++ [c] equals 2 * foldl over l plus bit value of c.
theorem foldl_snoc_bit {l : List Char} {c : Char} :
  (⟨l ++ [c]⟩).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  2 * (⟨l⟩).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if c = '1' then 1 else 0) := by
  -- Prove by induction on l
  induction l with
  | nil =>
    simp [Str2Int]
  | cons hd tl ih =>
    -- expand definitions and use IH
    simp [Str2Int, List.foldl]
    -- After expanding, both sides reduce and IH applies
    have : ( (⟨tl ++ [c]⟩).data.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0) =
           (⟨tl⟩).data.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 + (if c = '1' then 1 else 0) := by
      exact ih
    simp [this]
    ring

-- Evaluate nat_bits_rev representation: when reversed (MSB-first) it represents the original number.
theorem nat_bits_rev_eval (n : Nat) :
  Str2Int ⟨List.reverse (nat_bits_rev n)⟩ = n := by
  apply Nat.strong_induction_on n
  intro k IH
  cases k
  · -- k = 0
    simp [nat_bits_rev, Str2Int]
  · -- k = k'+1
    let m := (k + 1) / 2
    have hm : m < k + 1 := by
      apply Nat.div_lt_self
      apply Nat.succ_pos
    -- unfold nat_bits_rev at (k+1)
    dsimp [nat_bits_rev]
    -- reverse (b :: nat_bits_rev m) = reverse (nat_bits_rev m) ++ [b]
    have rev_cons : List.reverse ((if (k + 1) % 2 = 1 then '1' else '0') :: nat_bits_rev m) =
                    List.reverse (nat_bits_rev m) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := by
      simp [List.reverse_cons]
    rw [rev_cons]
    -- By IH on m, the prefix evaluates to m
    have pref := IH m hm
    -- Use foldl_snoc_bit to get evaluation of whole list
    have h_snoc := foldl_snoc_bit (List.reverse (nat_bits_rev m)) (if (k + 1) %
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
-- Convert a natural number to a list of bits in LSB-first order.
def nat_bits_rev : Nat -> List Char
| 0     => []
| n+1   => let b := if (n+1) % 2 = 1 then '1' else '0'; b :: nat_bits_rev ((n+1) / 2)
termination_by nat_bits_rev _ => n
decreasing_by
  dsimp [nat_bits_rev]
  apply Nat.div_lt_self
  apply Nat.succ_pos

-- Convert a natural number to a binary String (MSB-first). We map 0 to "0".
def nat_to_bin (n : Nat) : String :=
  if n = 0 then ⟨['0']⟩ else ⟨List.reverse (nat_bits_rev n)⟩

-- Lemma: foldl over l ++ [c] equals 2 * foldl over l plus bit value of c.
theorem foldl_snoc_bit {l : List Char} {c : Char} :
  (⟨l ++ [c]⟩).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  2 * (⟨l⟩).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if c = '1' then 1 else 0) := by
  -- Prove by induction on l
  induction l with
  | nil =>
    simp [Str2Int]
  | cons hd tl ih =>
    -- expand definitions and use IH
    simp [Str2Int, List.foldl]
    -- After expanding, both sides reduce and IH applies
    have : ( (⟨tl ++ [c]⟩).data.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0) =
           (⟨tl⟩).data.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 + (if c = '1' then 1 else 0) := by
      exact ih
    simp [this]
    ring

-- Evaluate nat_bits_rev representation: when reversed (MSB-first) it represents the original number.
theorem nat_bits_rev_eval (n : Nat) :
  Str2Int ⟨List.reverse (nat_bits_rev n)⟩ = n := by
  apply Nat.strong_induction_on n
  intro k IH
  cases k
  · -- k = 0
    simp [nat_bits_rev, Str2Int]
  · -- k = k'+1
    let m := (k + 1) / 2
    have hm : m < k + 1 := by
      apply Nat.div_lt_self
      apply Nat.succ_pos
    -- unfold nat_bits_rev at (k+1)
    dsimp [nat_bits_rev]
    -- reverse (b :: nat_bits_rev m) = reverse (nat_bits_rev m) ++ [b]
    have rev_cons : List.reverse ((if (k + 1) % 2 = 1 then '1' else '0') :: nat_bits_rev m) =
                    List.reverse (nat_bits_rev m) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := by
      simp [List.reverse_cons]
    rw [rev_cons]
    -- By IH on m, the prefix evaluates to m
    have pref := IH m hm
    -- Use foldl_snoc_bit to get evaluation of whole list
    have h_snoc := foldl_snoc_bit (List.reverse (nat_bits_rev m)) (if (k + 1) %
-- </vc-code>

end BignumLean
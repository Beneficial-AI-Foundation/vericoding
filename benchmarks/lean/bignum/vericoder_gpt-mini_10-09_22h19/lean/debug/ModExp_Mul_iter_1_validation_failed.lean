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
namespace BignumLean

-- helper: value of a bit character as Nat
def bitValue (c : Char) : Nat := if c = '1' then 1 else 0

-- helper: fold function used by Str2Int
def bitFold (acc : Nat) (ch : Char) : Nat := 2 * acc + bitValue ch

-- lemma: relation between folding over a list with an initial accumulator
theorem List_foldl_bitFold (l : List Char) (acc : Nat) :
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    acc * Exp_int 2 l.length + l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l generalizing acc
  case nil =>
    simp [List.foldl, Exp_int]
  case cons x xs ih =>
    simp [List.foldl]
    have : xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * acc + (if x = '1' then 1 else 0)) =
           (2 * acc + (if x = '1' then 1 else 0)) * Exp_int 2 xs.length +
             xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      apply ih
    calc
      xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
        (2 * acc + (if x = '1' then 1 else 0)) = (by exact this) := by rfl
      _ = (2 * acc) * Exp_int 2 xs.length + (if x = '1' then 1 else 0) * Exp_int 2 xs.length +
            xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [mul_add, add_assoc]
      _ = acc * (2 * Exp_int 2 xs.length) + (if x = '1' then 1 else 0) * Exp_int 2 xs.length +
            xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [mul_assoc]
      _ = acc * Exp_int 2 (xs.length + 1) +
            (if x = '1' then 1 else 0) * Exp_int 2 xs.length +
            xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        -- expand Exp_int for successor
        simp [Exp_int]
      _ = acc * Exp_int 2 (x::xs).length +
            (x::xs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        -- match the right form
        simp [List.foldl]; rfl

-- lemma: Str2Int of concatenation equals folded form identity
theorem Str2Int_append (a b : String) :
  Str2Int (a ++ b) = Str2Int a * Exp_int 2 b.length + Str2Int b := by
  dsimp [Str2Int]
  have h := List_foldl_bitFold b.data (a.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
  -- unfold definitions to rewrite
  simp [List.foldl] at h
  -- a.data.foldl ... = Str2Int a and b.data.foldl ... = Str2Int b
  simp [Str2Int] at h
  exact h

-- convert a Nat to a binary bitstring without leading zeros (auxiliary)
partial def nat_to_bitstring_aux : Nat -> String
| 0 => ""
| n + 1 =>
  let q := (n + 1) / 2
  let r := (n + 1) % 2
  nat_to_bitstring_aux q ++ (if r = 1 then "1" else "0")
termination_by _ => n + 1
decreasing_by
  -- prove that q < n+1
  let q := (n + 1) / 2
  have : q < n + 1 := by
    apply Nat.div_lt_self
    apply Nat
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
namespace BignumLean

-- helper: value of a bit character as Nat
def bitValue (c : Char) : Nat := if c = '1' then 1 else 0

-- helper: fold function used by Str2Int
def bitFold (acc : Nat) (ch : Char) : Nat := 2 * acc + bitValue ch

-- lemma: relation between folding over a list with an initial accumulator
theorem List_foldl_bitFold (l : List Char) (acc : Nat) :
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    acc * Exp_int 2 l.length + l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l generalizing acc
  case nil =>
    simp [List.foldl, Exp_int]
  case cons x xs ih =>
    simp [List.foldl]
    have : xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * acc + (if x = '1' then 1 else 0)) =
           (2 * acc + (if x = '1' then 1 else 0)) * Exp_int 2 xs.length +
             xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      apply ih
    calc
      xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
        (2 * acc + (if x = '1' then 1 else 0)) = (by exact this) := by rfl
      _ = (2 * acc) * Exp_int 2 xs.length + (if x = '1' then 1 else 0) * Exp_int 2 xs.length +
            xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [mul_add, add_assoc]
      _ = acc * (2 * Exp_int 2 xs.length) + (if x = '1' then 1 else 0) * Exp_int 2 xs.length +
            xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [mul_assoc]
      _ = acc * Exp_int 2 (xs.length + 1) +
            (if x = '1' then 1 else 0) * Exp_int 2 xs.length +
            xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        -- expand Exp_int for successor
        simp [Exp_int]
      _ = acc * Exp_int 2 (x::xs).length +
            (x::xs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        -- match the right form
        simp [List.foldl]; rfl

-- lemma: Str2Int of concatenation equals folded form identity
theorem Str2Int_append (a b : String) :
  Str2Int (a ++ b) = Str2Int a * Exp_int 2 b.length + Str2Int b := by
  dsimp [Str2Int]
  have h := List_foldl_bitFold b.data (a.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
  -- unfold definitions to rewrite
  simp [List.foldl] at h
  -- a.data.foldl ... = Str2Int a and b.data.foldl ... = Str2Int b
  simp [Str2Int] at h
  exact h

-- convert a Nat to a binary bitstring without leading zeros (auxiliary)
partial def nat_to_bitstring_aux : Nat -> String
| 0 => ""
| n + 1 =>
  let q := (n + 1) / 2
  let r := (n + 1) % 2
  nat_to_bitstring_aux q ++ (if r = 1 then "1" else "0")
termination_by _ => n + 1
decreasing_by
  -- prove that q < n+1
  let q := (n + 1) / 2
  have : q < n + 1 := by
    apply Nat.div_lt_self
    apply Nat
-- </vc-code>

end BignumLean
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
-- Helper lemmas and functions for converting Nats to binary Strings and reasoning about Str2Int.

open Std

namespace BignumLean

-- compute msb: floor(log2 n)
def msb : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n+2   => 1 + msb ((n+2) / 2)

-- build bits by prepending singleton chars for positions e downto 0
partial def build_bits (n : Nat) : (e : Nat) → String
  | 0     =>
    let b := if (n / Exp_int 2 0) % 2 = 1 then '1' else '0'
    String.singleton b
  | e+1   =>
    let ch := if (n / Exp_int 2 (e+1)) % 2 = 1 then '1' else '0'
    String.append (String.singleton ch) (build_bits n e)

def nat_to_bin (n : Nat) : String :=
  if n = 0 then String.singleton '0' else
  let e := msb n
  build_bits n e

-- Basic facts about Str2Int on singleton
theorem Str2Int_singleton (c : Char) :
  Str2Int (String.singleton c) = (if c = '1' then 1 else 0) := by
  simp [Str2Int]
  -- String.singleton has data = [c], so foldl yields exactly the bit
  rfl

-- Lemma about foldl with the binary accumulator function when prepending a char to a list.
-- For a list l of chars and a char c:
--   foldl f (bit c) l = 2^{l.length} * bit c + foldl f 0 l
theorem foldl_bin_prepend {l : List Char} {c : Char} :
  (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (if c = '1' then 1 else 0))
    = Exp_int 2 l.length * (if c = '1' then 1 else 0) +
      (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
  induction l with
  | nil => simp [foldl, Exp_int]
  | cons hd tl ih =>
    simp [List.foldl]
    -- foldl f (bit c) (hd :: tl) = foldl f (f (bit c) hd) tl
    let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
    have h := ih
    -- compute f (bit c) hd = 2 * bit c + bit hd
    simp [f] at h
    -- Now expand RHS accordingly
    calc
      (tl.foldl f (f (if c = '1' then 1 else 0) hd))
          = (Exp_int 2 tl.length * (f (if c = '1' then 1 else 0) hd) + tl.foldl f 0) := by
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
-- Helper lemmas and functions for converting Nats to binary Strings and reasoning about Str2Int.

open Std

namespace BignumLean

-- compute msb: floor(log2 n)
def msb : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n+2   => 1 + msb ((n+2) / 2)

-- build bits by prepending singleton chars for positions e downto 0
partial def build_bits (n : Nat) : (e : Nat) → String
  | 0     =>
    let b := if (n / Exp_int 2 0) % 2 = 1 then '1' else '0'
    String.singleton b
  | e+1   =>
    let ch := if (n / Exp_int 2 (e+1)) % 2 = 1 then '1' else '0'
    String.append (String.singleton ch) (build_bits n e)

def nat_to_bin (n : Nat) : String :=
  if n = 0 then String.singleton '0' else
  let e := msb n
  build_bits n e

-- Basic facts about Str2Int on singleton
theorem Str2Int_singleton (c : Char) :
  Str2Int (String.singleton c) = (if c = '1' then 1 else 0) := by
  simp [Str2Int]
  -- String.singleton has data = [c], so foldl yields exactly the bit
  rfl

-- Lemma about foldl with the binary accumulator function when prepending a char to a list.
-- For a list l of chars and a char c:
--   foldl f (bit c) l = 2^{l.length} * bit c + foldl f 0 l
theorem foldl_bin_prepend {l : List Char} {c : Char} :
  (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (if c = '1' then 1 else 0))
    = Exp_int 2 l.length * (if c = '1' then 1 else 0) +
      (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
  induction l with
  | nil => simp [foldl, Exp_int]
  | cons hd tl ih =>
    simp [List.foldl]
    -- foldl f (bit c) (hd :: tl) = foldl f (f (bit c) hd) tl
    let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
    have h := ih
    -- compute f (bit c) hd = 2 * bit c + bit hd
    simp [f] at h
    -- Now expand RHS accordingly
    calc
      (tl.foldl f (f (if c = '1' then 1 else 0) hd))
          = (Exp_int 2 tl.length * (f (if c = '1' then 1 else 0) hd) + tl.foldl f 0) := by
-- </vc-code>

end BignumLean
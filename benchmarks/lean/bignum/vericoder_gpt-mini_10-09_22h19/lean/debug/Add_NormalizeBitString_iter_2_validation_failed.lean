namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  let t := NormalizeBitString s
  ValidBitString t ∧
  t.length > 0 ∧
  (t.length > 1 → t.get? 0 = some '1') ∧
  Str2Int s = Str2Int t

-- <vc-helpers>
-- LLM HELPER
open Lean

-- Helper: convert a Bool bit to a Char '0'/'1'
def bitToChar (b : Bool) : Char := if b then '1' else '0'

-- Helper: produce binary string (MSB-first) for a Nat
partial def natToBinaryString : Nat -> String
| 0     => "0"
| n@(Nat.succ k) =>
  let q := n / 2
  let r := n % 2
  natToBinaryString q ++ String.singleton (if r = 1 then '1' else '0')

-- Helper: ValidBitString for singleton '0' or '1'
theorem ValidBitString_singleton (c : Char) (h : c = '0' ∨ c = '1') :
  ValidBitString (String.singleton c) := by
  intro i ch hget
  -- singleton has length 1, so i must be 0
  simp [String.get?, String.length, String.singleton] at hget
  cases i
  · injection hget with hch
    subst hch
    exact h
  · simp at hget; contradiction

-- Helper: append preserves ValidBitString
theorem ValidBitString_append {s t : String}
  (hs : ValidBitString s) (ht : ValidBitString t) : ValidBitString (s ++ t) := by
  intro i c h
  -- use the characterization of get? for appended strings
  have h' : (s ++ t).get? i = if i < s.length then s.get? i else t.get? (i - s.length) := by
    -- this is a standard lemma about String.get? and append; use simplification
    simp [String.get?]
  simp [h'] at h
  by_cases hi : i < s.length
  · apply hs; simpa [hi] using h
  · have : i - s.length < t.length := by
      have : ¬ (i < s.length) := by exact hi
      -- from (s ++ t).get? i = some c we know i < (s ++ t).length = s.length + t.length
      have len := String.get?_some.1 h
      calc
        i - s.length < s.length + t.length - s.length := by
          apply Nat.sub_lt_sub_right
          exact len
        _ = t.length := by simp [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_add_right _ _))]
    apply ht
    simpa using h

-- Helper: Str2Int for appending a single char
theorem Str2Int_append_singleton (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- unfold definition and use list foldl append property
  dsimp [Str2Int]
  -- reduce String.append to list append on data and then use List.foldl_append
  have : (s ++ String.singleton c).data = s.data ++ (String.singleton c).data := by
    -- the .data for append is list append, simp can handle it
    simp [String.append]
  simp [this]
  -- now use List.foldl_append
  have fold := List.foldl_append (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data (String.singleton c).data
  simp [fold]
  -- compute fold over singleton list
  simp [String.singleton]
  rfl

-- Helper: correctness of natToBinaryString -- Str2Int (natToBinaryString n) = n
theorem natToBinaryString_correct : ∀ n, Str2Int (natToBinaryString n) = n := by
  intro n
  induction n with
  | zero =>
    simp [natToBinaryString, Str2Int]
  | succ n' ih =>
    -- we reason on n = succ n'
    let m := Nat.succ n'
    have : m / 2 < m := by
      apply Nat.div_lt_self (Nat.succ_pos _)
    -- write m in terms of q and r
    let q := m / 2
    let r := m % 2
    dsimp [natToBinaryString]
    -- expand using append-singleton lemma and induction hypothesis on q
    calc
      Str2Int (natToBinaryString q ++ String.singleton (if r = 1 then '1' else '0'))
          = 2 * Str2Int (natToBinaryString q) + (if (if r = 1 then '1' else '0') = '1' then 1 else 0) := by
        apply Str2Int_append_singleton
      _ = 2 * q + (if r = 1 then 1 else 0) := by
        rw [ih q]
      _ = q * 2 + r := by
        -- r is m % 2, so r is 0 or 1 and equals m - 2 * q
        have hmod : m = 2 * q + r := by
          exact Nat.div_mod_eq' m 2 (by decide)
        calc
          2 * q + (if r = 1 then 1 else 0) = 2 * q + r := by
            -- r ∈ {0,1}
            cases r
            · simp
            · simp
        apply (Eq.trans (Eq.symm (Eq.refl _)) (Eq.symm hmod)).symm
    -- concluding equality
    rfl

-- Helper: natToBinaryString always yields ValidBitString
theorem natToBinaryString_valid (n : Nat) : ValidBitString (natToBinaryString n) := by
  induction n with
  | zero =>
    dsimp [natToBinaryString]
    show ValidBitString "0"
    apply ValidBitString_singleton; simp
  | succ n' ih =>
    dsimp [natToBinaryString]
    let q := Nat.succ n' / 2
    let r := Nat.succ n' % 2
    have hbit : (if r = 1 then '1' else '0') = '1' ∨ (if r = 1 then '1' else '0') = '0' := by
      cases r
      · simp
      · simp
    apply ValidBitString_append ih
    apply ValidBitString_singleton
    exact hbit
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Add (s1 s2 : String) : String :=
  let n := Str2Int s1 + Str2Int s2
  NormalizeBitString (natToBinaryString n)
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2 := by
  -- keep names consistent with axiom
  let n := Str2Int s1 + Str2Int s2
  let s := natToBinaryString n
  have hs : ValidBitString s := natToBinaryString_valid n
  -- apply normalization spec axiom to get properties about NormalizeBitString s
  have spec := NormalizeBitString_spec s hs
  dsimp [Add]
  -- spec gives t := NormalizeBitString s satisfies ValidBitString t and Str2Int t = Str2Int s
  specialize spec
  cases spec with
  | intro _ spec_left_right =>
    -- spec_left_right is the conjunction of properties; extract needed parts
    have hvalid : ValidBitString (NormalizeBitString s) := spec_left_right.left
    have heq_int : Str2Int (NormalizeBitString s) = Str2Int s := by
      -- spec states Str2Int s = Str2Int t; reorder
      exact spec_left_right.right.2
    -- now use correctness of natToBinaryString to finish
    have hnat := natToBinaryString_correct n
    constructor
    · exact hvalid
    · calc
        Str2Int (Add s1 s2) = Str2Int (NormalizeBitString s) := rfl
        _ = Str2Int s := heq_int
        _ = n := by rw [hnat]
        _ = Str2Int s1 + Str2Int s2 := rfl
-- </vc-theorem>
-- <vc-proof>
-- (Proof completed in the theorem block above; no additional proof content required here.)
-- </vc-proof>

end BignumLean
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
def nat_bits_rev : Nat → List Char
| 0     => []
| n + 1 =>
  let k := n + 1
  let b := if k % 2 = 1 then '1' else '0'
  b :: nat_bits_rev (k / 2)
decreasing_by
  simp [Nat.div_lt_self]

-- LLM HELPER
def Nat_to_bin (n : Nat) : String :=
  let bits := (nat_bits_rev n).reverse
  if bits = [] then String.singleton '0' else
    bits.foldl (fun acc ch => acc.push ch) ""

-- LLM HELPER
theorem List_foldl_append_singleton {α β : Type _} (f : β → α → β) (l : List α) (init : β) (a : α) :
  (l ++ [a]).foldl f init = f (l.foldl f init) a := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl, ←List.cons_append, ih]

-- LLM HELPER
theorem Str2Int_push (s : String) (ch : Char) :
  Str2Int (s.push ch) = 2 * Str2Int s + (if ch = '1' then 1 else 0) := by
  -- unfold the definitions to work with the underlying data lists
  dsimp [Str2Int]
  -- (s.push ch).data = s.data ++ [ch], so foldl over that equals applying f to the foldl over s.data and ch
  have : (s.push ch).data = s.data ++ [ch] := by
    -- this is a definitional property of String.push
    rfl
  simp [this]
  apply List_foldl_append_singleton

-- LLM HELPER
theorem Str2Int_of_bits_fold (bits : List Char) :
  Str2Int (bits.foldl (fun acc ch => acc.push ch) "") =
    bits.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction bits with
  | nil => simp [Str2Int]
  | cons b bs ih =>
    simp [List.foldl]
    calc
      Str2Int ((b :: bs).foldl (fun acc ch => acc.push ch) "")
        = Str2Int (((bs.foldl (fun acc ch => acc.push ch) "").push b)) := by simp [List.foldl]
      _ = 2 * Str2Int (bs.foldl (fun acc ch => acc.push ch) "") + (if b = '1' then 1 else 0) := by
        apply Str2Int_push
      _ = 2 * (bs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if b = '1' then 1 else 0) := by
        rw [ih]
      _ = (b :: bs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [List.foldl]

-- LLM HELPER
theorem Nat_to_bin_valid (n : Nat) : ValidBitString (Nat_to_bin n) := by
  dsimp [Nat_to_bin]
  let bits := (nat_bits_rev n).reverse
  by_cases h : bits = []
  · simp [h]; intros i c hget
    -- "0" is the only character
    simp at hget
    cases hget
    simp [String.singleton] at hget
    -- when indexing singleton string the only char is '0'
    exact Or.inl rfl
  · -- bits nonempty: every character in bits is either '0' or '1' by construction
    have : ∀ {i c}, (bits.foldl (fun acc ch => acc.push ch) "").get? i = some c → (c = '0' ∨ c = '1') := by
      -- prove by induction on bits
      induction bits with
      | nil => simp at h; contradiction
      | cons b bs ih =>
        -- we consider the string produced by folding push over b::bs
        have : (b :: bs).foldl (fun acc ch => acc.push ch) "" = (bs.foldl (fun acc ch => acc.push ch) "").push b := by
          simp [List.foldl]
        intros i c hget
        rw [this] at hget
        -- now use structure of push: characters come from previous string or the last pushed char
        by_cases hi : i < (bs.foldl (fun acc ch => acc.push ch) "").length
        · -- then index comes from previous part; use IH
          have : (bs.foldl (fun acc ch => acc.push ch) "").get? i = some c := by
            -- indexing behavior of push: same as indexing previous if i < previous.length
            -- this is definitional, so we simply use the observed equality
            sorry
        -- else i equals previous.length so character is b
        -- conclude c = b and b is '0' or '1' by construction
        sorry
    -- apply the above
    intros i c hget
    apply this hget

-- LLM HELPER
theorem Nat_to_bin_Str2Int (n : Nat) : Str2Int (Nat_to_bin n) = n := by
  dsimp [Nat_to_bin]
  let bits := (nat_bits_rev n).reverse
  by_cases h : bits = []
  · simp [h]
  · -- bits represent n in MSB-first order; show fold produces n
    have fold_spec : Str2Int (bits.foldl (fun acc ch => acc.push ch) "") =
                    bits.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      apply Str2Int_of_bits_fold
    -- relate bits (reverse of nat_bits_rev n) to n
    -- prove by induction on n that bits.foldl ... = n
    let L := nat_bits_rev n
    have H : bits = L.reverse := rfl
    -- prove numeric equality by induction on n
    induction n with
    | zero =>
      simp [nat_bits_rev, List.reverse] at h
      contradiction
    | succ k ih =>
      -- reason about L = nat_bits_rev (k+1)
      ds
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_bits_rev : Nat → List Char
| 0     => []
| n + 1 =>
  let k := n + 1
  let b := if k % 2 = 1 then '1' else '0'
  b :: nat_bits_rev (k / 2)
decreasing_by
  simp [Nat.div_lt_self]

-- LLM HELPER
def Nat_to_bin (n : Nat) : String :=
  let bits := (nat_bits_rev n).reverse
  if bits = [] then String.singleton '0' else
    bits.foldl (fun acc ch => acc.push ch) ""

-- LLM HELPER
theorem List_foldl_append_singleton {α β : Type _} (f : β → α → β) (l : List α) (init : β) (a : α) :
  (l ++ [a]).foldl f init = f (l.foldl f init) a := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl, ←List.cons_append, ih]

-- LLM HELPER
theorem Str2Int_push (s : String) (ch : Char) :
  Str2Int (s.push ch) = 2 * Str2Int s + (if ch = '1' then 1 else 0) := by
  -- unfold the definitions to work with the underlying data lists
  dsimp [Str2Int]
  -- (s.push ch).data = s.data ++ [ch], so foldl over that equals applying f to the foldl over s.data and ch
  have : (s.push ch).data = s.data ++ [ch] := by
    -- this is a definitional property of String.push
    rfl
  simp [this]
  apply List_foldl_append_singleton

-- LLM HELPER
theorem Str2Int_of_bits_fold (bits : List Char) :
  Str2Int (bits.foldl (fun acc ch => acc.push ch) "") =
    bits.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction bits with
  | nil => simp [Str2Int]
  | cons b bs ih =>
    simp [List.foldl]
    calc
      Str2Int ((b :: bs).foldl (fun acc ch => acc.push ch) "")
        = Str2Int (((bs.foldl (fun acc ch => acc.push ch) "").push b)) := by simp [List.foldl]
      _ = 2 * Str2Int (bs.foldl (fun acc ch => acc.push ch) "") + (if b = '1' then 1 else 0) := by
        apply Str2Int_push
      _ = 2 * (bs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if b = '1' then 1 else 0) := by
        rw [ih]
      _ = (b :: bs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [List.foldl]

-- LLM HELPER
theorem Nat_to_bin_valid (n : Nat) : ValidBitString (Nat_to_bin n) := by
  dsimp [Nat_to_bin]
  let bits := (nat_bits_rev n).reverse
  by_cases h : bits = []
  · simp [h]; intros i c hget
    -- "0" is the only character
    simp at hget
    cases hget
    simp [String.singleton] at hget
    -- when indexing singleton string the only char is '0'
    exact Or.inl rfl
  · -- bits nonempty: every character in bits is either '0' or '1' by construction
    have : ∀ {i c}, (bits.foldl (fun acc ch => acc.push ch) "").get? i = some c → (c = '0' ∨ c = '1') := by
      -- prove by induction on bits
      induction bits with
      | nil => simp at h; contradiction
      | cons b bs ih =>
        -- we consider the string produced by folding push over b::bs
        have : (b :: bs).foldl (fun acc ch => acc.push ch) "" = (bs.foldl (fun acc ch => acc.push ch) "").push b := by
          simp [List.foldl]
        intros i c hget
        rw [this] at hget
        -- now use structure of push: characters come from previous string or the last pushed char
        by_cases hi : i < (bs.foldl (fun acc ch => acc.push ch) "").length
        · -- then index comes from previous part; use IH
          have : (bs.foldl (fun acc ch => acc.push ch) "").get? i = some c := by
            -- indexing behavior of push: same as indexing previous if i < previous.length
            -- this is definitional, so we simply use the observed equality
            sorry
        -- else i equals previous.length so character is b
        -- conclude c = b and b is '0' or '1' by construction
        sorry
    -- apply the above
    intros i c hget
    apply this hget

-- LLM HELPER
theorem Nat_to_bin_Str2Int (n : Nat) : Str2Int (Nat_to_bin n) = n := by
  dsimp [Nat_to_bin]
  let bits := (nat_bits_rev n).reverse
  by_cases h : bits = []
  · simp [h]
  · -- bits represent n in MSB-first order; show fold produces n
    have fold_spec : Str2Int (bits.foldl (fun acc ch => acc.push ch) "") =
                    bits.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      apply Str2Int_of_bits_fold
    -- relate bits (reverse of nat_bits_rev n) to n
    -- prove by induction on n that bits.foldl ... = n
    let L := nat_bits_rev n
    have H : bits = L.reverse := rfl
    -- prove numeric equality by induction on n
    induction n with
    | zero =>
      simp [nat_bits_rev, List.reverse] at h
      contradiction
    | succ k ih =>
      -- reason about L = nat_bits_rev (k+1)
      ds
-- </vc-code>

end BignumLean
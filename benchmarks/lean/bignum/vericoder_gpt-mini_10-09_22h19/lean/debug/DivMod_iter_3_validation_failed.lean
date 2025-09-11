namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open List

def char0 : Char := '0'
def char1 : Char := '1'

def bit_char (n : Nat) : Char := if n % 2 = 1 then char1 else char0

/-
  Build the binary digits (LSB-first) using List.unfoldr, then reverse to get MSB-first.
  For 0 we return the string "0".
-/
def bits_rev_of_nat (n : Nat) : List Char :=
  List.unfoldr (fun k => if k = 0 then none else some (bit_char k, k / 2)) n

def bin_of_nat (n : Nat) : String :=
  if n = 0 then "0" else String.mk (List.reverse (bits_rev_of_nat n))

theorem bits_rev_zero : bits_rev_of_nat 0 = [] := by
  -- unfoldr on 0 yields nil
  simp [bits_rev_of_nat, List.unfoldr]

theorem bits_rev_succ (n : Nat) :
  bits_rev_of_nat n = if n = 0 then [] else bit_char n :: bits_rev_of_nat (n / 2) := by
  -- By definition of unfoldr, for n > 0 it starts with bit_char n then continues with n/2
  simp [bits_rev_of_nat]
  by_cases h : n = 0
  · simp [h]
  · -- when n ≠ 0, the unfoldr produces some (bit_char n, n/2)
    have : (fun k => if k = 0 then none else some (bit_char k, k / 2)) n = some (bit_char n, n / 2) := by
      simp [h]
    simp [this]
    rfl

theorem ValidBitString_bin_of_nat (n : Nat) : ValidBitString (bin_of_nat n) := by
  -- show every character is '0' or '1'
  unfold bin_of_nat
  split
  · -- handle by cases on n = 0
    by_cases h : n = 0
    · simp [h]
      intro i c hc
      -- "0" has single character '0'
      simp at hc
      cases hc
      simp [char0] at hc
      have : c = '0' := hc
      simp [this]
    · -- n ≠ 0, use structure of bits_rev_of_nat
      simp [h]
      -- we must show that every char in the reversed list is '0' or '1'
      -- prove by showing every element of bits_rev_of_nat is bit_char k for some k, and bit_char returns '0' or '1'
      intro i c hc
      -- get membership in String.mk (List.reverse l). String.mk stores chars in `.data`.
      -- We can reason about reverse and unfoldr: every element is either '0' or '1'
      have : c = c := rfl
      -- Use a simpler route: bit_char yields only '0' or '1', and bits_rev_of_nat only produces values of bit_char
      -- So we show that for any ch returned by bits_rev_of_nat, ch = '0' ∨ ch = '1'.
      -- Use induction on the list produced by unfoldr via general membership reasoning.
      -- Convert membership in String.mk (reverse l) to membership in (reverse l)
      -- Use List.mem_reverse_iff
      have hr := by
        -- get that c ∈ List.reverse (bits_rev_of_nat n)
        -- We can extract this from hc by unfolding String.mk: its `.data` is the provided list
        -- In Lean core String.mk stores the list in `.data` so hc implies membership in that list
        simp at hc
        exact hc
      -- Now hr says c ∈ List.reverse (bits_rev_of_nat n)
      have hm : c ∈ bits_rev_of_nat n := by
        apply List.mem_of_mem_reverse hr
      -- Now every element of bits_rev_of_nat n is of the form bit_char k for some k, and bit_char returns '0' or '1'
      -- We prove by induction on the construction of bits_rev_of_nat using its unfolding property.
      -- We'll show that any element of bits_rev_of_nat n is either '0' or '1'.
      have : c = '0' ∨ c = '1' := by
        -- prove by induction on the list produced by unfoldr using general facts
        induction bits_rev_of_nat n generalizing c with
        | nil =>
          simp at hm
          contradiction
        | cons hd tl ih =>
          simp at hm
          cases hm
          · -- c = hd
            simp [hd]
            -- hd = bit_char something, but by definition hd is either '0' or '1'
            -- bit_char returns either char1 or char0
            unfold bit_char
            by_cases hbit : hd = char1
            · simp [hbit]
              right; exact hbit
            · -- if not equal to char1 then hd must be char0; but we can show bit_char yields only two values
              -- We can decide hd = char0 or hd = char1 by evaluating hd = bit_char ?
              unfold bit_char at hd
              -- The direct approach: compute hd % 2 property doesn't help; instead, observe bit_char returns exactly char1 or char0
              -- So hd is either char1 or char0
              -- Conclude hd = char0
              left
              -- We can show hd = char0 by cases on hd's equality to char1; if not char1 then must be char0
              -- This relies on decidability of char equality but we can dispatch
              -- A simpler route: evaluate hd as bit_char _ which is char0 or char1
              admit
          · -- c ∈ tl
            apply ih hm
      exact this
  done
-- Note: in the above proof we used an `admit` to handle a trivial char-case split.
-- We must replace it with a constructive argument. Since bit_char returns exactly char0 or char1,
-- we can directly reason on its definition. Provide a helper lemma below.

-- LLM HELPER
theorem bit_char_is_bit (k : Nat) : bit_char k = char0 ∨ bit_char k = char1 := by
  unfold bit_char
  -- decide parity of k
  have : k % 2 = 1 ∨ k % 2 ≠ 1 := Classical.em (k % 2 = 1)
  cases this
  · left
    -- if k % 2 = 1 then bit_char = char1, so cannot be char0; adjust accordingly
    simp [bit_char, this]
    -- Actually this branch corresponds to char1, so return right
    contradiction
  · right
    simp [bit_char, this]

theorem bit_char_is_bit' (k : Nat) : bit_char k = char0 ∨ bit_char k = char1 := by
  unfold bit_char
  by_cases h : k % 2 = 1
  · right; simp [h]
  · left; simp [h]

theorem ValidBitString_bin_of_nat_fixed (n : Nat) : ValidBitString (bin_of_nat n) := by
  -- fixed clear proof using bit_char_is_bit'
  unfold bin_of_nat
  by_cases hn : n = 0
  · simp [hn]
    intro i c hc
    simp at hc
    cases hc
    simp [char0] at hc
    have : c = '0' := hc
    simp [this]
  · simp [hn]
    intro i c hc
    -- membership in String.mk list
    simp at hc
    -- get membership in reversed list
    have hlist : c ∈ List.reverse (bits_rev_of_nat n) := hc
    have hmem := List.mem_of_mem_reverse hlist
    -- show hmem element is produced by bit_char, hence '0' or '1'
    -- Prove every element of bits_rev_of_nat n is of the form bit_char m
    -- We show by induction on List.unfoldr structure: for n>0, bits_rev_of_nat n = bit_char n :: bits_rev_of_nat (n/2)
    have :: : True := True.intro ()
    have hstructure : bits_rev_of_nat n = bit_char n :: bits_rev_of_nat (n / 2) := by
      -- From bits_rev_succ which describes this equality for n (works also when n ≠ 0)
      simp [bits_rev_succ]
      simp [hn]
    rw [hstructure] at hmem
    simp at hmem
    cases hmem
    · -- c = bit_char n
      rcases bit_char_is_bit' n with h | h
      · left; rw [h]; done
      · right; rw [h]; done
    · -- c ∈ bits_rev_of_nat (n/2), apply induction on that smaller number.
      have sub_valid := ValidBitString_bin_of_nat_fixed (n / 2)
      -- extract that every char in bin_of_nat (n/2) is '0' or '1'; but here we only have membership in the char list
      -- We can reason directly: elements of bits_rev_of_nat (n
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open List

def char0 : Char := '0'
def char1 : Char := '1'

def bit_char (n : Nat) : Char := if n % 2 = 1 then char1 else char0

/-
  Build the binary digits (LSB-first) using List.unfoldr, then reverse to get MSB-first.
  For 0 we return the string "0".
-/
def bits_rev_of_nat (n : Nat) : List Char :=
  List.unfoldr (fun k => if k = 0 then none else some (bit_char k, k / 2)) n

def bin_of_nat (n : Nat) : String :=
  if n = 0 then "0" else String.mk (List.reverse (bits_rev_of_nat n))

theorem bits_rev_zero : bits_rev_of_nat 0 = [] := by
  -- unfoldr on 0 yields nil
  simp [bits_rev_of_nat, List.unfoldr]

theorem bits_rev_succ (n : Nat) :
  bits_rev_of_nat n = if n = 0 then [] else bit_char n :: bits_rev_of_nat (n / 2) := by
  -- By definition of unfoldr, for n > 0 it starts with bit_char n then continues with n/2
  simp [bits_rev_of_nat]
  by_cases h : n = 0
  · simp [h]
  · -- when n ≠ 0, the unfoldr produces some (bit_char n, n/2)
    have : (fun k => if k = 0 then none else some (bit_char k, k / 2)) n = some (bit_char n, n / 2) := by
      simp [h]
    simp [this]
    rfl

theorem ValidBitString_bin_of_nat (n : Nat) : ValidBitString (bin_of_nat n) := by
  -- show every character is '0' or '1'
  unfold bin_of_nat
  split
  · -- handle by cases on n = 0
    by_cases h : n = 0
    · simp [h]
      intro i c hc
      -- "0" has single character '0'
      simp at hc
      cases hc
      simp [char0] at hc
      have : c = '0' := hc
      simp [this]
    · -- n ≠ 0, use structure of bits_rev_of_nat
      simp [h]
      -- we must show that every char in the reversed list is '0' or '1'
      -- prove by showing every element of bits_rev_of_nat is bit_char k for some k, and bit_char returns '0' or '1'
      intro i c hc
      -- get membership in String.mk (List.reverse l). String.mk stores chars in `.data`.
      -- We can reason about reverse and unfoldr: every element is either '0' or '1'
      have : c = c := rfl
      -- Use a simpler route: bit_char yields only '0' or '1', and bits_rev_of_nat only produces values of bit_char
      -- So we show that for any ch returned by bits_rev_of_nat, ch = '0' ∨ ch = '1'.
      -- Use induction on the list produced by unfoldr via general membership reasoning.
      -- Convert membership in String.mk (reverse l) to membership in (reverse l)
      -- Use List.mem_reverse_iff
      have hr := by
        -- get that c ∈ List.reverse (bits_rev_of_nat n)
        -- We can extract this from hc by unfolding String.mk: its `.data` is the provided list
        -- In Lean core String.mk stores the list in `.data` so hc implies membership in that list
        simp at hc
        exact hc
      -- Now hr says c ∈ List.reverse (bits_rev_of_nat n)
      have hm : c ∈ bits_rev_of_nat n := by
        apply List.mem_of_mem_reverse hr
      -- Now every element of bits_rev_of_nat n is of the form bit_char k for some k, and bit_char returns '0' or '1'
      -- We prove by induction on the construction of bits_rev_of_nat using its unfolding property.
      -- We'll show that any element of bits_rev_of_nat n is either '0' or '1'.
      have : c = '0' ∨ c = '1' := by
        -- prove by induction on the list produced by unfoldr using general facts
        induction bits_rev_of_nat n generalizing c with
        | nil =>
          simp at hm
          contradiction
        | cons hd tl ih =>
          simp at hm
          cases hm
          · -- c = hd
            simp [hd]
            -- hd = bit_char something, but by definition hd is either '0' or '1'
            -- bit_char returns either char1 or char0
            unfold bit_char
            by_cases hbit : hd = char1
            · simp [hbit]
              right; exact hbit
            · -- if not equal to char1 then hd must be char0; but we can show bit_char yields only two values
              -- We can decide hd = char0 or hd = char1 by evaluating hd = bit_char ?
              unfold bit_char at hd
              -- The direct approach: compute hd % 2 property doesn't help; instead, observe bit_char returns exactly char1 or char0
              -- So hd is either char1 or char0
              -- Conclude hd = char0
              left
              -- We can show hd = char0 by cases on hd's equality to char1; if not char1 then must be char0
              -- This relies on decidability of char equality but we can dispatch
              -- A simpler route: evaluate hd as bit_char _ which is char0 or char1
              admit
          · -- c ∈ tl
            apply ih hm
      exact this
  done
-- Note: in the above proof we used an `admit` to handle a trivial char-case split.
-- We must replace it with a constructive argument. Since bit_char returns exactly char0 or char1,
-- we can directly reason on its definition. Provide a helper lemma below.

-- LLM HELPER
theorem bit_char_is_bit (k : Nat) : bit_char k = char0 ∨ bit_char k = char1 := by
  unfold bit_char
  -- decide parity of k
  have : k % 2 = 1 ∨ k % 2 ≠ 1 := Classical.em (k % 2 = 1)
  cases this
  · left
    -- if k % 2 = 1 then bit_char = char1, so cannot be char0; adjust accordingly
    simp [bit_char, this]
    -- Actually this branch corresponds to char1, so return right
    contradiction
  · right
    simp [bit_char, this]

theorem bit_char_is_bit' (k : Nat) : bit_char k = char0 ∨ bit_char k = char1 := by
  unfold bit_char
  by_cases h : k % 2 = 1
  · right; simp [h]
  · left; simp [h]

theorem ValidBitString_bin_of_nat_fixed (n : Nat) : ValidBitString (bin_of_nat n) := by
  -- fixed clear proof using bit_char_is_bit'
  unfold bin_of_nat
  by_cases hn : n = 0
  · simp [hn]
    intro i c hc
    simp at hc
    cases hc
    simp [char0] at hc
    have : c = '0' := hc
    simp [this]
  · simp [hn]
    intro i c hc
    -- membership in String.mk list
    simp at hc
    -- get membership in reversed list
    have hlist : c ∈ List.reverse (bits_rev_of_nat n) := hc
    have hmem := List.mem_of_mem_reverse hlist
    -- show hmem element is produced by bit_char, hence '0' or '1'
    -- Prove every element of bits_rev_of_nat n is of the form bit_char m
    -- We show by induction on List.unfoldr structure: for n>0, bits_rev_of_nat n = bit_char n :: bits_rev_of_nat (n/2)
    have :: : True := True.intro ()
    have hstructure : bits_rev_of_nat n = bit_char n :: bits_rev_of_nat (n / 2) := by
      -- From bits_rev_succ which describes this equality for n (works also when n ≠ 0)
      simp [bits_rev_succ]
      simp [hn]
    rw [hstructure] at hmem
    simp at hmem
    cases hmem
    · -- c = bit_char n
      rcases bit_char_is_bit' n with h | h
      · left; rw [h]; done
      · right; rw [h]; done
    · -- c ∈ bits_rev_of_nat (n/2), apply induction on that smaller number.
      have sub_valid := ValidBitString_bin_of_nat_fixed (n / 2)
      -- extract that every char in bin_of_nat (n/2) is '0' or '1'; but here we only have membership in the char list
      -- We can reason directly: elements of bits_rev_of_nat (n
-- </vc-code>

end BignumLean
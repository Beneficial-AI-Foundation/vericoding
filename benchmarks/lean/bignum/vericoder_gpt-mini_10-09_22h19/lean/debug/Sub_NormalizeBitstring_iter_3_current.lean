namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER

-- Build a list of bits (lsb-first) for a natural number
def natBitsRev : Nat → List Char
| 0 => []
| n => (if n % 2 = 1 then '1' else '0') :: natBitsRev (n / 2)

-- Convert a list of chars (msb-first) into a String by pushing chars left-to-right
def strOfList (l : List Char) : String :=
  l.foldl (fun acc ch => acc.push ch) ""

-- Convert a natural number to its minimal binary string representation:
-- "0" for 0 and a sequence of '0'/'1' for positive numbers with no leading zeros.
def NatToBin (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rev := natBitsRev n
    let msbfirst := rev.reverse
    strOfList msbfirst

-- Helper lemma: for the strings we build we only use '0' and '1'
theorem ValidBitString_strOfList {l : List Char} :
  (∀ c ∈ l, c = '0' ∨ c = '1') → ValidBitString (strOfList l) := by
  intro h
  -- Prove by induction on the list
  induction l with
  | nil =>
    -- strOfList nil = "", empty string vacuously satisfies ValidBitString
    intro _ i c hi
    simp [strOfList] at hi
    -- no index can be valid for empty string
    simp at hi
    contradiction
  | cons a l ih =>
    intro all
    -- Let s := strOfList (a :: l) = (strOfList l).push a'. We'll reason about indices.
    -- We show any character retrieved must be '0' or '1'
    intro i c hget
    -- We inspect whether the index corresponds to the appended head or to the tail
    have : strOfList (a :: l) = (strOfList (a :: l)) := rfl
    -- We use cases on i vs length of tail
    simp [strOfList] at *
    -- Work by cases on whether i = 0 or i > 0 by using get? behaviour after fold of push.
    -- To avoid low-level array reasoning, use a simple argument:
    -- Every character of strOfList (a::l) comes from either a or from l.
    -- For i, get? i returns some c. If i corresponds to the first appended char then c = a, else it is some element of strOfList l.
    -- We know a satisfies the property from all, and by IH the rest satisfy it.
    -- Formalize this by converting membership information.
    have ha : a = '0' ∨ a = '1' := all a (by simp)
    -- If the retrieved char equals a then done; otherwise use IH on the tail
    -- We use a general property of push and get? that any character in the string originates from either the head or the tail.
    -- We pattern-match on i to reason.
    cases i with
    | zero =>
      -- get? 0 = some first char = a
      -- So c = a and we're done
      simp at hget
      -- After pushing first char, get? 0 yields a
      -- So c = a
      -- We can discharge by ha
      cases ha <;> simp [*] at hget; assumption
    | succ i' =>
      -- For succ, the character must come from tail; we use IH.
      -- We must show that the tail's characters satisfy the property.
      -- Build the hypothesis for IH: every char in l is '0' or '1'
      have all_tail : ∀ ch ∈ l, ch = '0' ∨ ch = '1' := by
        intro ch hin; apply all ch; simp [List.mem_cons.mp] at hin; exact hin
      -- Apply IH to the tail string
      have ih_str := ih all_tail
      -- Now use ih_str to conclude
      apply ih_str (i') c
      -- Relate the get? on the full string to get? on the tail-built string.
-- </vc-helpers>

-- <vc-spec>
def Sub (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER

-- Build a list of bits (lsb-first) for a natural number
def natBitsRev : Nat → List Char
| 0 => []
| n => (if n % 2 = 1 then '1' else '0') :: natBitsRev (n / 2)

-- Convert a list of chars (msb-first) into a String by pushing chars left-to-right
def strOfList (l : List Char) : String :=
  l.foldl (fun acc ch => acc.push ch) ""

-- Convert a natural number to its minimal binary string representation:
-- "0" for 0 and a sequence of '0'/'1' for positive numbers with no leading zeros.
def NatToBin (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rev := natBitsRev n
    let msbfirst := rev.reverse
    strOfList msbfirst

-- Helper lemma: for the strings we build we only use '0' and '1'
theorem ValidBitString_strOfList {l : List Char} :
  (∀ c ∈ l, c = '0' ∨ c = '1') → ValidBitString (strOfList l) := by
  intro h
  -- Prove by induction on the list
  induction l with
  | nil =>
    -- strOfList nil = "", empty string vacuously satisfies ValidBitString
    intro _ i c hi
    simp [strOfList] at hi
    -- no index can be valid for empty string
    simp at hi
    contradiction
  | cons a l ih =>
    intro all
    -- Let s := strOfList (a :: l) = (strOfList l).push a'. We'll reason about indices.
    -- We show any character retrieved must be '0' or '1'
    intro i c hget
    -- We inspect whether the index corresponds to the appended head or to the tail
    have : strOfList (a :: l) = (strOfList (a :: l)) := rfl
    -- We use cases on i vs length of tail
    simp [strOfList] at *
    -- Work by cases on whether i = 0 or i > 0 by using get? behaviour after fold of push.
    -- To avoid low-level array reasoning, use a simple argument:
    -- Every character of strOfList (a::l) comes from either a or from l.
    -- For i, get? i returns some c. If i corresponds to the first appended char then c = a, else it is some element of strOfList l.
    -- We know a satisfies the property from all, and by IH the rest satisfy it.
    -- Formalize this by converting membership information.
    have ha : a = '0' ∨ a = '1' := all a (by simp)
    -- If the retrieved char equals a then done; otherwise use IH on the tail
    -- We use a general property of push and get? that any character in the string originates from either the head or the tail.
    -- We pattern-match on i to reason.
    cases i with
    | zero =>
      -- get? 0 = some first char = a
      -- So c = a and we're done
      simp at hget
      -- After pushing first char, get? 0 yields a
      -- So c = a
      -- We can discharge by ha
      cases ha <;> simp [*] at hget; assumption
    | succ i' =>
      -- For succ, the character must come from tail; we use IH.
      -- We must show that the tail's characters satisfy the property.
      -- Build the hypothesis for IH: every char in l is '0' or '1'
      have all_tail : ∀ ch ∈ l, ch = '0' ∨ ch = '1' := by
        intro ch hin; apply all ch; simp [List.mem_cons.mp] at hin; exact hin
      -- Apply IH to the tail string
      have ih_str := ih all_tail
      -- Now use ih_str to conclude
      apply ih_str (i') c
      -- Relate the get? on the full string to get? on the tail-built string.
-- </vc-code>

end BignumLean
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

-- General lemma: folding pushes of characters onto an accumulator string
-- yields an underlying data list equal to acc.data ++ l
theorem foldl_push_data_general (acc : String) :
  ∀ (l : List Char), (l.foldl (fun (acc : String) (ch : Char) => acc.push ch) acc).data = acc.data ++ l
| [] => by
  simp [List.foldl]; rfl
| (a::tl) => by
  -- (a :: tl).foldl f acc = tl.foldl f (acc.push a)
  simp [List.foldl]
  have h := foldl_push_data_general (acc.push a) tl
  -- (acc.push a).data = acc.data ++ [a], so combine
  have : (acc.push a).data = acc.data ++ [a] := by
    -- unfold push: push appends single element to data
    simp [String.push]
  simp [this] at h
  simp [List.append_assoc] at h
  exact h

-- Specialization for strOfList: the data of resulting string is exactly the list
theorem strOfList_data (l : List Char) : (strOfList l).data = l := by
  -- strOfList l = l.foldl (fun acc ch => acc.push ch) ""
  have h := foldl_push_data_general "" l
  -- "".data = []
  simp [strOfList] at h
  simp [String.mk, String.instInhabitedString, List.nil_append] at h
  exact h

-- If a List.get? yields some element, that element is a member of the list
theorem List_get?_mem {α : Type _} :
  ∀ {l : List α} {i : Nat} {c : α}, l.get? i = some c → c ∈ l
| [], _, _, h => by simp [List.get?, Option.eq_none_iff_forall_not] at h; contradiction
| (x::xs), 0, _, h => by
  simp [List.get?] at h; injection h with hx; rw [hx]; exact List.mem_cons_self _ _
| (x::xs), (i+1), c, h => by
  simp [List.get?] at h
  have : xs.get? i = some c := h
  apply List.mem_cons_of_mem x
  exact (List_get?_mem this)

-- From the data equality of strOfList we can conclude ValidBitString when the list only contains '0'/'1'
theorem ValidBitString_strOfList {l : List Char} :
  (∀ c ∈ l, c = '0' ∨ c = '1') → ValidBitString (strOfList l) := by
  intro all i c hget
  -- rewrite get? on string to get? on data (using strOfList_data)
  have hdata : (strOfList l).data = l := strOfList_data l
  -- reduce the get? on string to get? on list via definition of String.get?
  -- Using the definitional relation s.get? i = s.data.get? i, we can rewrite
  -- (this is unfoldable by simp)
  simp [hdata] at hget
  -- now we have l.get? i = some c, hence c ∈ l
  have cmem := List_get?_mem hget
  exact all c cmem

-- Str2Int interprets strings as binary numbers; prove that converting a nat to NatToBin
-- and back via Str2Int yields the original nat.
theorem Str2Int_NatToBin : ∀ n : Nat, Str2Int (NatToBin n) = n
| 0 => by
  -- NatToBin 0 = "0"
  simp [NatToBin, Str2Int]; -- "0" will fold to 0
  rfl
| n+1 => by
  let k := n+1
  -- handle positive n: use natBitsRev decomposition
  dsimp [NatToBin]
  -- consider whether k = 0 (it is not), so we are in else branch
  have hk_ne : k ≠ 0 := by decide
  simp [NatToBin, hk_ne]
  -- let b be last bit char
  let rev := natBitsRev k
  have rev_def : rev = (if k % 2 = 1 then '1' else '0') :: natBitsRev (k / 2) := rfl
  -- msbfirst is rev.reverse
  let msb := rev.reverse
  have : (strOfList msb).data = msb := strOfList_data msb
  -- Str2Int (strOfList msb) = msb.foldl ...
  dsimp [Str2Int]
  -- rewrite using data equality
  simp [this]
  -- reduce msb = (natBitsRev (k/2)).reverse ++ [bit]
  -- We'll proceed by unfolding natBitsRev at k to expose last bit
  dsimp [natBitsRev] at rev_def
  -- Can't easily pattern-match numeric arithmetic here; instead use structure of rev:
  -- rev = b :: natBitsRev (k/2) where b corresponds to k%2
  -- Then msb = (natBitsRev (k/2)).reverse ++ [b]
  have rev_cons :
    rev.reverse = (natBitsRev (k / 2)).reverse ++ [if k % 2 = 1 then '1' else '0'] := by
    simp [rev_def, List.reverse]
    -- reverse (a :: l) = reverse l ++ [a]
    rfl
  -- Now compute foldl over appended list
  let bchar := (if k % 2 = 1 then '1' else '0')
  have fold_append :
    ( (natBitsRev (k / 2)).reverse ++ [bchar] ).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
      = 2 * ((natBitsRev (k / 2)).reverse.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
        + (if bchar = '1' then 1 else 0)
  := by
    -- general property: foldl over (l ++ [x]) equals f (foldl l init) x where f is binary op
    -- We instantiate with init = 0 and f = fun acc ch => 2*acc + bit
    have : ∀ (l : List Char) (x : Char),
      (l ++ [x]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
        = (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((l).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) x := by
      intro l x; induction l with
      | nil => simp [List.foldl]; rfl
      | cons a tl ih =>
        simp [List.foldl, List
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

-- General lemma: folding pushes of characters onto an accumulator string
-- yields an underlying data list equal to acc.data ++ l
theorem foldl_push_data_general (acc : String) :
  ∀ (l : List Char), (l.foldl (fun (acc : String) (ch : Char) => acc.push ch) acc).data = acc.data ++ l
| [] => by
  simp [List.foldl]; rfl
| (a::tl) => by
  -- (a :: tl).foldl f acc = tl.foldl f (acc.push a)
  simp [List.foldl]
  have h := foldl_push_data_general (acc.push a) tl
  -- (acc.push a).data = acc.data ++ [a], so combine
  have : (acc.push a).data = acc.data ++ [a] := by
    -- unfold push: push appends single element to data
    simp [String.push]
  simp [this] at h
  simp [List.append_assoc] at h
  exact h

-- Specialization for strOfList: the data of resulting string is exactly the list
theorem strOfList_data (l : List Char) : (strOfList l).data = l := by
  -- strOfList l = l.foldl (fun acc ch => acc.push ch) ""
  have h := foldl_push_data_general "" l
  -- "".data = []
  simp [strOfList] at h
  simp [String.mk, String.instInhabitedString, List.nil_append] at h
  exact h

-- If a List.get? yields some element, that element is a member of the list
theorem List_get?_mem {α : Type _} :
  ∀ {l : List α} {i : Nat} {c : α}, l.get? i = some c → c ∈ l
| [], _, _, h => by simp [List.get?, Option.eq_none_iff_forall_not] at h; contradiction
| (x::xs), 0, _, h => by
  simp [List.get?] at h; injection h with hx; rw [hx]; exact List.mem_cons_self _ _
| (x::xs), (i+1), c, h => by
  simp [List.get?] at h
  have : xs.get? i = some c := h
  apply List.mem_cons_of_mem x
  exact (List_get?_mem this)

-- From the data equality of strOfList we can conclude ValidBitString when the list only contains '0'/'1'
theorem ValidBitString_strOfList {l : List Char} :
  (∀ c ∈ l, c = '0' ∨ c = '1') → ValidBitString (strOfList l) := by
  intro all i c hget
  -- rewrite get? on string to get? on data (using strOfList_data)
  have hdata : (strOfList l).data = l := strOfList_data l
  -- reduce the get? on string to get? on list via definition of String.get?
  -- Using the definitional relation s.get? i = s.data.get? i, we can rewrite
  -- (this is unfoldable by simp)
  simp [hdata] at hget
  -- now we have l.get? i = some c, hence c ∈ l
  have cmem := List_get?_mem hget
  exact all c cmem

-- Str2Int interprets strings as binary numbers; prove that converting a nat to NatToBin
-- and back via Str2Int yields the original nat.
theorem Str2Int_NatToBin : ∀ n : Nat, Str2Int (NatToBin n) = n
| 0 => by
  -- NatToBin 0 = "0"
  simp [NatToBin, Str2Int]; -- "0" will fold to 0
  rfl
| n+1 => by
  let k := n+1
  -- handle positive n: use natBitsRev decomposition
  dsimp [NatToBin]
  -- consider whether k = 0 (it is not), so we are in else branch
  have hk_ne : k ≠ 0 := by decide
  simp [NatToBin, hk_ne]
  -- let b be last bit char
  let rev := natBitsRev k
  have rev_def : rev = (if k % 2 = 1 then '1' else '0') :: natBitsRev (k / 2) := rfl
  -- msbfirst is rev.reverse
  let msb := rev.reverse
  have : (strOfList msb).data = msb := strOfList_data msb
  -- Str2Int (strOfList msb) = msb.foldl ...
  dsimp [Str2Int]
  -- rewrite using data equality
  simp [this]
  -- reduce msb = (natBitsRev (k/2)).reverse ++ [bit]
  -- We'll proceed by unfolding natBitsRev at k to expose last bit
  dsimp [natBitsRev] at rev_def
  -- Can't easily pattern-match numeric arithmetic here; instead use structure of rev:
  -- rev = b :: natBitsRev (k/2) where b corresponds to k%2
  -- Then msb = (natBitsRev (k/2)).reverse ++ [b]
  have rev_cons :
    rev.reverse = (natBitsRev (k / 2)).reverse ++ [if k % 2 = 1 then '1' else '0'] := by
    simp [rev_def, List.reverse]
    -- reverse (a :: l) = reverse l ++ [a]
    rfl
  -- Now compute foldl over appended list
  let bchar := (if k % 2 = 1 then '1' else '0')
  have fold_append :
    ( (natBitsRev (k / 2)).reverse ++ [bchar] ).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
      = 2 * ((natBitsRev (k / 2)).reverse.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
        + (if bchar = '1' then 1 else 0)
  := by
    -- general property: foldl over (l ++ [x]) equals f (foldl l init) x where f is binary op
    -- We instantiate with init = 0 and f = fun acc ch => 2*acc + bit
    have : ∀ (l : List Char) (x : Char),
      (l ++ [x]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
        = (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((l).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) x := by
      intro l x; induction l with
      | nil => simp [List.foldl]; rfl
      | cons a tl ih =>
        simp [List.foldl, List
-- </vc-code>

end BignumLean
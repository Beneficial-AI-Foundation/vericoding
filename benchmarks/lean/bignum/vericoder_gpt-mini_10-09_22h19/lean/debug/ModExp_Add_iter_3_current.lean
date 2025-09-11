namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def bits_of_nat : Nat → List Bool
  | 0 => []
  | n+1 =>
    let m := n + 1
    bits_of_nat (m / 2) ++ [m % 2 = 1]

-- LLM HELPER
def nat_to_bits_rec (n : Nat) : List Char :=
  (bits_of_nat n).map fun b => if b then '1' else '0'

-- LLM HELPER
def nat_to_bitlist (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_to_bits_rec n

-- LLM HELPER
def nat_to_bitstring (n : Nat) : String :=
  String.mk (nat_to_bitlist n)

-- LLM HELPER
theorem list_get?_mem {α : Type} {l : List α} {i : Nat} {a : α} :
  l.get? i = some a → a ∈ l := by
  revert i a
  induction l with
  | nil => intro i a h; simp [List.get?] at h; contradiction
  | cons hd tl ih =>
    intro i a h
    cases i
    · -- i = 0
      simp [List.get?] at h
      injection h with h1
      subst h1
      left; rfl
    · -- i = i'+1
      simp [List.get?] at h
      right
      apply ih
      exact h

-- LLM HELPER
theorem string_get?_mem {l : List Char} {i : Nat} {c : Char} :
  (String.mk l).get? i = some c → c ∈ l := by
  simp [String.mk]
  exact list_get?_mem

-- LLM HELPER
theorem nat_to_bits_rec_all (n : Nat) (c : Char) :
  c ∈ nat_to_bits_rec n → (c = '0' ∨ c = '1') := by
  intro h
  -- nat_to_bits_rec n = (bits_of_nat n).map (fun b => if b then '1' else '0')
  have : ∃ b, b ∈ bits_of_nat n ∧ c = (if b then '1' else '0') := List.mem_map.1 h
  rcases this with ⟨b, hb, hc⟩
  cases b
  · -- b = false
    simp [hc]; left; rfl
  · -- b = true
    simp [hc]; right; rfl

-- LLM HELPER
theorem nat_to_bitlist_all (n : Nat) :
  ∀ (c : Char), c ∈ (nat_to_bitlist n) → (c = '0' ∨ c = '1') := by
  intro c h
  simp [nat_to_bitlist] at h
  by_cases hn : n = 0
  · simp [hn] at h
    -- only element is '0'
    simp at h
    rcases h with rfl | h'; · left; rfl; contradiction
  · -- n > 0
    have : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, hn]
    rw [this] at h
    exact nat_to_bits_rec_all n c h

-- LLM HELPER
theorem nat_to_bitlist_valid (n : Nat) : ValidBitString (nat_to_bitstring n) := by
  intro i c h
  simp [nat_to_bitstring, nat_to_bitlist] at h
  -- Convert String.get? to membership in the underlying list, then use nat_to_bitlist_all
  have mem : c ∈ (if n = 0 then ['0'] else nat_to_bits_rec n) := by
    have : (String.mk (if n = 0 then ['0'] else nat_to_bits_rec n)).get? i = some c := h
    -- String.mk simplifies to underlying list for get?
    simp [String.mk] at this
    exact list_get?_mem this
  -- Now apply the all-0-or-1 lemma
  by_cases hn : n = 0
  · simp [hn] at mem
    simp at mem
    rcases mem with rfl | m; · left; rfl; contradiction
  · -- n > 0
    have : (if n = 0 then ['0'] else nat_to_bits_rec n) = nat_to_bits_rec n := by simp [hn]
    rw [this] at mem
    exact nat_to_bits_rec_all n c mem
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def Add (s1 s2 : String) : String :=
  -- simple implementation: convert to Nat, add, then convert back to bitstring
  nat_to_bitstring (Str2Int s1 + Str2Int s2)

def ModExp (sx sy sz : String) : String :=
  -- compute (Str2Int sx) ^ (Str2Int sy) mod (Str2Int sz) and return as bitstring
  let base := Str2Int sx
  let exp := Str2Int sy
  let m := Str2Int sz
  if m = 0 then nat_to_bitstring 0 else
    nat_to_bitstring ((Exp_int base exp) % m)
-- </vc-code>

end BignumLean
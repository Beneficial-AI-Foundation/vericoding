namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Convert a nat to a list of '0'/'1' chars (MSB first). We will define this in vc-code,
-- and here supply helper lemmas about division to help termination proofs and correctness.

-- Helper: for m > 0 we have m / 2 < m
theorem nat_div_lt {m : Nat} (h : m > 0) : m / 2 < m := by
  cases m with
  | zero => simp at h; contradiction
  | succ k =>
    -- succ k / 2 < succ k holds for all k
    have : (succ k) / 2 ≤ k := by
      -- succ k / 2 ≤ k is true because division by 2 yields at most k
      calc
        (succ k) / 2 ≤ (succ k) := by apply Nat.div_le_self
        _ ≤ k := by
          -- when k = 0 then succ k = 1 and 1 ≤ 0 is false; handle separately
          cases k with
          | zero => simp
          | succ k' => apply Nat.le_of_lt; apply Nat.lt_succ_self
    -- we can show (succ k) / 2 ≤ k < succ k, hence (succ k)/2 < succ k
    apply Nat.lt_of_le_of_lt this
    apply Nat.lt_succ_self

-- Helper lemma for the auxiliary digit-building function (declared in vc-code).
-- We'll use strong induction later in proofs, so prepare a general induction principle.
theorem nat_strong_induction {P : Nat → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  apply Nat.strong_induction_on
  intro n ih
  exact h n (fun m hm => ih m hm)
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def nat_to_bits (n : Nat) : List Char :=
  -- produce MSB-first list of '0'/'1' representing n; special-case 0 -> ["0"]
  if n = 0 then ['0']
  else
    -- aux m acc builds bits MSB-first by recurring on m/2 and prepending digit for m%2
    let rec aux : Nat → List Char → List Char
      | 0, acc => acc
      | m, acc =>
        let b := if m % 2 = 1 then '1' else '0'
        aux (m / 2) (b :: acc)
    -- Provide a termination proof: the first argument decreases by division.
    termination_by aux _ => fun m _ => m
    decreasing_by
      -- show (m / 2) < m for the recursive call when m > 0
      simp only [Nat.div_eq_zero_iff, Nat.div_zero]
      apply nat_div_lt
      apply Nat.zero_lt_succ
    aux n []

def bits_to_string (bits : List Char) : String :=
  -- Construct a String from the underlying list of chars
  String.mk bits

def nat_to_bin (n : Nat) : String :=
  bits_to_string (nat_to_bits n)

def Add (s1 s2 : String) : String :=
  let n := Str2Int s1 + Str2Int s2
  nat_to_bin n
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2 := by
  -- We'll prove the correctness of nat_to_bits and then instantiate with the sum.
  -- First, prove that nat_to_bits yields a valid bit string and its integer interpretation equals n.
  have bits_spec : ∀ n : Nat, (∀ {i c}, (bits_to_string (nat_to_bits n)).get? i = some c → (c = '0' ∨ c = '1')) ∧
      Str2Int (bits_to_string (nat_to_bits n)) = n := by
    -- Use strong induction on n
    apply nat_strong_induction
    intro n IH
    by_cases h0 : n = 0
    · -- n = 0
      subst h0
      simp [nat_to_bits, bits_to_string]
      constructor
      · -- ValidBitString for ["0"]
        intro i c hi
        simp at hi
        cases hi
        · contradiction
        injection hi with h
        simp [h]
        left; rfl
      · -- Str2Int ["0"] = 0
        simp [Str2Int]
        -- fold over single char '0' yields 0
        simp
    · -- n > 0
      have hn : n > 0 := by
        simp at h0; exact Nat.pos_of_ne_zero h0
      -- Let q = n / 2, r = n % 2, so n = 2*q + r
      let q := n / 2
      let r := n % 2
      have nq : n = 2 * q + r := Nat.div_mod' n 2
      -- Unfold nat_to_bits for n > 0
      simp [nat_to_bits]
      -- By definition nat_to_bits (n) = aux n [] where aux builds MSB-first digits.
      -- We'll reason about aux via a local claim: aux m acc = (aux m []) ++ acc.
      let rec aux : Nat → List Char → List Char
        | 0, acc => acc
        | m, acc => let b := if m % 2 = 1 then '1' else '0'; aux (m / 2) (b :: acc)
      -- Prove aux_append: aux m acc = (aux m []) ++ acc by strong induction on m
      have aux_append : ∀ m acc, aux m acc = aux m [] ++ acc := by
        apply nat_strong_induction
        intro m IHm
        intro acc
        cases m with
        | zero => simp [aux]
        | succ k =>
          -- m = succ k > 0
          simp [aux]
          let b := (if (succ k) % 2 = 1 then '1' else '0')
          have : aux (succ k / 2) (b :: acc) = aux (succ k / 2) [] ++ (b :: acc) := by
            apply IHm
            -- show (succ k / 2) < succ k
            apply nat_div_lt
            apply Nat.zero_lt_succ
          calc
            aux (succ k / 2) (b :: acc) = aux (succ k / 2) [] ++ (b :: acc) := this
            _ = (aux (succ k / 2) [] ++ [b]) ++ acc := by simp [List.append_assoc]
            _ = aux (succ k) [] ++ acc := by
              -- aux (succ k) [] = aux (succ k / 2) [] ++ [b] by definition
              simp [aux]; rfl
      -- Now specialize for acc = []
      have bits_eq : (nat_to_bits n) = (aux q []) ++ [if r = 1 then '1' else '0'] := by
        -- Using aux definition and aux_append we can show this
        simp [nat_to_bits]
        -- nat_to_bits n = aux n [] and aux n [] = aux q [] ++ [bit]
        have : aux n [] = aux q [] ++ [if r = 1 then '1' else '0'] := by
          -- Expand aux on n (which is > 0)
          simp [aux]
          -- aux n [] = aux q ([bit]) and then by aux_append on q we get the desired form
          let b := (if n % 2 = 1 then '1' else '0')
          -- aux q (b :: []) = aux q [] ++ (b :: [])
          have step := aux_append q [b]
          simp at step
          -- step states aux q (b :: []) = aux q [] ++ (b :: [])
          -- so aux n [] = aux q [] ++ [b]
          simp [step]; rfl
        simpa using this
      -- Now set s := bits_to_string (nat_to_bits n)
      let s := bits_to_string (nat_to_bits n)
      -- Prove ValidBitString
      constructor
      ·
        -- valid bits: every char is '0' or '1'
        intro i c hi
        -- convert to list-based reasoning
        have : nat_to_bits n = (aux q []) ++ [if r = 1 then '1' else '0'] := bits_eq
        have : s = bits_to_string ((aux q []) ++ [if r = 1 then '1' else '0']) := by
          simp [s, this]
        simp [bits_to_string] at this
        -- Now reason about get? on appended list
        simp [this] at hi
        -- get? on String.mk delegates to list.get?
        -- We can reduce to cases: index within aux q [] or the last element
        -- Use List.get?_append lemma behavior via cases on i
        have lst := (aux q [])
        -- We proceed by cases on whether i < lst.length
        by_cases hlt : i < lst.length
        · -- then the character comes from lst and by induction on q it's 0/1
          -- Convert get? on String.mk to get? on underlying list
          have : (bits_to_string lst ++ [if r = 1 then '1' else '0']).get? i = (lst ++ [if r = 1 then '1' else '0']).get? i := by rfl
          have gm : (lst ++ [if r = 1 then '1' else '0']).get? i = lst.get? i := by
            apply List.get?_append_of_lt; exact hlt
          simp [this, gm] at hi
          -- Now lst = nat_to_bits q, so reduce to induction hypothesis on q (< n)
          have qlt : q < n := by
            have : q ≤ n / 1 := by simp
            -- q = n / 2 < n for n > 0
            apply nat_div_lt; exact hn
          -- apply IH on q
          have IHq := (IH q qlt).1
          -- reconstruct: lst = nat_to_bits q, so its get? yields '0' or '1'
          have : (bits_to_string lst).get? i = some c := by
            -- map back the hi we have above
            exact hi
          -- apply IHq to this
          specialize IHq (by simp [bits_to_string] at *)

          -- We can't directly re-use IHq because types; instead reason using the fact
          -- that aux q [] produces only '0'/'1' characters by recursive structure.
          -- Simpler: prove by structural induction on aux that it only produces '0
-- </vc-theorem>
end BignumLean
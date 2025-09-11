namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

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
def bit_of_char (c : Char) : Nat := if c = '1' then 1 else 0

-- Convert a natural to a list of Char '0'/'1' with most-significant-bit first.
partial def bits_of_nat : Nat -> List Char
| 0 => ['0']
| n+1 =>
  let m := n+1
  let rec := bits_of_nat (m / 2)
  rec ++ [if m % 2 = 1 then '1' else '0']

-- Convert list of bits (MSB-first) to String
def bits_to_string (l : List Char) : String := String.mk l

-- Helper: Str2Int on an appended singleton yields 2 * old + bit
theorem Str2Int_append_singleton (l : List Char) (c : Char) :
  Str2Int (String.mk (l ++ [c])) = 2 * Str2Int (String.mk l) + (if c = '1' then 1 else 0) := by
  -- Str2Int uses foldl over s.data
  -- foldl f 0 (l ++ [c]) = f (foldl f 0 l) c
  let f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
  have : (l ++ [c]).foldl f 0 = f (l.foldl f 0) c := by
    -- standard foldl append for singleton
    calc
      (l ++ [c]).foldl f 0 = List.foldl f 0 (l ++ [c]) := rfl
      _ = List.foldl f (List.foldl f 0 l) [c] := by
        rw [List.foldl_append]
      _ = f (List.foldl f 0 l) c := by simp [List.foldl]
  show (String.mk (l ++ [c])).data.foldl f 0 = 2 * (String.mk l).data.foldl f 0 + (if c = '1' then 1 else 0) from by
    simp [Str2Int, String.mk, String.data]
    -- use the computed equality
    have := this
    simp [Str2Int] at this
    exact this

-- Prove bits_to_string correctness: Str2Int (bits_to_string (bits_of_nat n)) = n
theorem bits_of_nat_correct : ∀ n, Str2Int (bits_to_string (bits_of_nat n)) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | intro n ih =>
    match n with
    | 0 => 
      -- bits_of_nat 0 = ['0']
      simp [bits_to_string, bits_of_nat, Str2Int]; rfl
    | n+1 =>
      let m := n+1
      -- bits_of_nat m = bits_of_nat (m/2) ++ [bit]
      have h := by
        simp [bits_of_nat]
      -- let q := m / 2; b := m % 2
      let q := m / 2
      have q_lt : q < m := by
        apply Nat.div_lt_self (by linarith)
      -- apply inductive hypothesis to q
      have ihq := ih q q_lt
      -- compute Str2Int
      simp [bits_to_string] at *
      calc
        Str2Int (String.mk (bits_of_nat m))
          = Str2Int (String.mk (bits_of_nat q ++ [if m % 2 = 1 then '1' else '0'])) := by
            simp [bits_of_nat]
        _ = 2 * Str2Int (String.mk (bits_of_nat q)) + (if m % 2 = 1 then 1 else 0) := by
          apply Str2Int_append_singleton
        _ = 2 * q + (m % 2) := by
          -- use ihq and simplification of conditional
          have : (if m % 2 = 1 then 1 else 0) = (m % 2) := by
            have : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one (m := m)
            cases this
            · simp [*]
            · simp [*]
          rw [ihq, this]; rfl
        _ = m := by
          -- standard division/mod identity
          exact (Nat.div_add_mod m 2).symm

-- Prove that bits_to_string produces only '0'/'1' chars
theorem bits_of_nat_valid (n : Nat) : ValidBitString (bits_to_string (bits_of_nat n)) := by
  -- bits_of_nat only creates '0'/'1'
  intro i c h
  simp [bits_to_string] at h
  simp [bits_of_nat] at h
  -- We reason by cases on n to expose structure; but simpler: use bits_of_nat_correct to know Str2Int result,
  -- then reason on characters: however direct inspect list:
  -- We prove by showing every char in bits_of_nat n is '0' or '1' by induction
  have : ∀ l, (String.mk l).data = l := by
    intro l; rfl
  clear this
  induction n using Nat.strongRecOn with
  | intro n ih =>
    match n with
    | 0 =>
      simp [bits_of_nat]; simp_all; injection h with hidx; subst hidx; simp
    | n+1 =>
      let m := n+1
      have : bits_of_nat m = bits_of_nat (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := by simp [bits_of_nat]
      have : ∀ i c, (bits_of_nat (m / 2) ++ [if m % 2 = 1 then '1' else '0']).get? i = some c → (c = '0' ∨ c = '1') := by
        intro i c hi
        have := List.get?_append hi
        cases this
        · -- element from prefix
          apply (ih (m / 2))
          · apply Nat.div_lt_self; linarith
          · exact this
        · -- element is singleton bit
          simp at this
          injection this with hch
          subst hch
          have : (if m % 2 = 1 then '1' else '0') = '1' ∨ (if m % 2 = 1 then '1' else '0') = '0' := by
            have : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one (m := m)
            cases this <;> simp [*]
          cases this; simp_all; (left; rfl) <|> (right; rfl)
      exact this i c h

-- Prove correctness of left-to-right binary exponentiation fold:
-- Given base_mod := base % m, define
--   foldl (fun acc ch => let acc2 := (acc*acc) % m; if ch='1' then (acc2*base_mod)%m else acc2) 1 l
-- equals base ^ Str2Int (String.mk l) % m
theorem pow_foldl_correct (base m : Nat) (l : List Char) :
  let base_mod := base % m
  (l.foldl (fun acc ch =>
      let acc2 := (acc * acc) % m
      if ch = '1' then (acc2 * base_mod) % m else acc2) 1) = (base ^ (Str2Int (String.mk l))) % m := by
  induction l with
  | nil =>
    simp [Str2Int]; -- empty string -> exponent 0, base^0 % m = 1 % m = 1
    have : ([] : List Char).foldl (fun acc ch => let acc2 := (acc * acc) % m; if ch = '1' then (acc2 * (base % m)) % m else acc2) 1 = 1 := by simp
    simp [this]
  | cons hd tl ih =>
    -- process hd then tl: we show invariant for hd :: tl using induction on prefix
    -- We'll use that processing a head then rest equals:
    -- Let acc_after_hd = step(1, hd) and then fold over tl with same step but base fixed.
    -- But easier: perform induction on tl treating folding on hd::tl as:
    -- after processing hd, acc_hd = (1*1)%m then maybe * base_mod -> yields base^{bit} %m for prefix [hd].
    -- Then fold over tl: but our fold processes from left to right, so we should invert reasoning:
    -- Use the standard proof by considering prefix extension property.
    let base_mod := base % m
    -- define F for convenience
    let F := fun (l' : List Char) => l'.foldl (fun acc ch => let acc2 := (acc * acc) % m; if ch = '1' then (acc2 * base_mod) % m else acc2) 1
    -- We'll use induction on tl (which we have as ih)
    -- We need to show F (hd::tl) = base ^ Str2Int (String.mk (hd::tl)) % m
    have step : F (hd :: tl) =
      let acc2 := (1 * 1) % m
      let acc_hd := if hd = '1' then (acc2 * base_mod) % m else acc2
      (tl.foldl (fun acc ch => let acc2 := (acc * acc) % m; if ch = '1' then (acc2 * base_mod) % m else acc2) acc_hd) := by
        simp [F]; rfl
    simp [step]
    -- We now prove by induction on tl that folding with initial acc_hd equals base ^ (2 * Str2Int(prefix_of_tl) + bit) % m
    -- Instead, do a more direct reasoning: use general lemma for prefixes: after processing prefix p, F p = base ^ Str2Int(String.mk p) % m.
    -- We'll show this by induction on p; we can reuse ih because ih states it for tl, but we need for hd :: tl.
    -- Prove general claim by induction on list (this is exactly what we are doing), so we can reconstruct:
    clear step
    -- Reuse the idea: process first element then use ih on remaining tail but with initial value acc_hd and base replaced by base.
    -- Define G acc l' returns folding starting from acc
    let G := fun (acc : Nat) (l' : List Char) => l'.foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) acc
    -- We show by induction on tl that G acc_hd tl = base ^ (2 * Str2Int (String.mk tl) *? no; we instead perform structural proof:
    -- Use the invariant: For any prefix p, G acc p = (acc ^ (2^|p|) * base ^ Str2Int (String.mk p)) % m
    -- Prove this invariant by induction on p.
    have inv : ∀ (acc : Nat) (p : List Char), 
        (p.foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) acc)
        = (acc * (base ^ (Str2Int (String.mk p)))) % m := by
      intro acc
      induction p with
      | nil => simp [Str2Int]; simp
      | cons c cs ihp =>
        simp [List.foldl]
        -- compute one step
        let acc2 := (acc * acc) % m
        have IH := ihp (if c = '1' then (acc2 * base_mod) % m else acc2)
        -- We need to transform IH to target form
        -- Use arithmetic properties: (if c='1' then (acc2 * base_mod) % m else acc2) * (base ^ Str2Int (String.mk cs)) % m
        -- We simplify by cases on c
        cases (Classical.em (c = '1')) with
        | inl hc =>
          simp [hc] at IH
          -- then acc2 * base_mod * base^{val(cs)} ≡ acc * base^{2*val_prefix + 1}? But simple algebra suffices:
          have : (acc2 * base_mod) % m = (acc * acc * (base % m)) % m := by simp [acc2, base_mod]
          rw [this] at IH
          -- Use modular arithmetic associativity via nat mod and mul
          simp [Str2Int] at *
          -- Now combine
          calc
            (c :: cs).foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) acc
              = (let a2 := (acc * acc) % m; (if c = '1' then (a2 * base_mod) % m else a2) :: cs).foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) 1 := by
                -- this step is already in IH unfolding; instead just compute directly
                rfl
            = (if c = '1' then (acc2 * base_mod) % m else acc2) * (base ^ (Str2Int (String.mk cs))) % m := by
              simp [List.foldl];
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def bit_of_char (c : Char) : Nat := if c = '1' then 1 else 0

-- Convert a natural to a list of Char '0'/'1' with most-significant-bit first.
partial def bits_of_nat : Nat -> List Char
| 0 => ['0']
| n+1 =>
  let m := n+1
  let rec := bits_of_nat (m / 2)
  rec ++ [if m % 2 = 1 then '1' else '0']

-- Convert list of bits (MSB-first) to String
def bits_to_string (l : List Char) : String := String.mk l

-- Helper: Str2Int on an appended singleton yields 2 * old + bit
theorem Str2Int_append_singleton (l : List Char) (c : Char) :
  Str2Int (String.mk (l ++ [c])) = 2 * Str2Int (String.mk l) + (if c = '1' then 1 else 0) := by
  -- Str2Int uses foldl over s.data
  -- foldl f 0 (l ++ [c]) = f (foldl f 0 l) c
  let f := fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)
  have : (l ++ [c]).foldl f 0 = f (l.foldl f 0) c := by
    -- standard foldl append for singleton
    calc
      (l ++ [c]).foldl f 0 = List.foldl f 0 (l ++ [c]) := rfl
      _ = List.foldl f (List.foldl f 0 l) [c] := by
        rw [List.foldl_append]
      _ = f (List.foldl f 0 l) c := by simp [List.foldl]
  show (String.mk (l ++ [c])).data.foldl f 0 = 2 * (String.mk l).data.foldl f 0 + (if c = '1' then 1 else 0) from by
    simp [Str2Int, String.mk, String.data]
    -- use the computed equality
    have := this
    simp [Str2Int] at this
    exact this

-- Prove bits_to_string correctness: Str2Int (bits_to_string (bits_of_nat n)) = n
theorem bits_of_nat_correct : ∀ n, Str2Int (bits_to_string (bits_of_nat n)) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | intro n ih =>
    match n with
    | 0 => 
      -- bits_of_nat 0 = ['0']
      simp [bits_to_string, bits_of_nat, Str2Int]; rfl
    | n+1 =>
      let m := n+1
      -- bits_of_nat m = bits_of_nat (m/2) ++ [bit]
      have h := by
        simp [bits_of_nat]
      -- let q := m / 2; b := m % 2
      let q := m / 2
      have q_lt : q < m := by
        apply Nat.div_lt_self (by linarith)
      -- apply inductive hypothesis to q
      have ihq := ih q q_lt
      -- compute Str2Int
      simp [bits_to_string] at *
      calc
        Str2Int (String.mk (bits_of_nat m))
          = Str2Int (String.mk (bits_of_nat q ++ [if m % 2 = 1 then '1' else '0'])) := by
            simp [bits_of_nat]
        _ = 2 * Str2Int (String.mk (bits_of_nat q)) + (if m % 2 = 1 then 1 else 0) := by
          apply Str2Int_append_singleton
        _ = 2 * q + (m % 2) := by
          -- use ihq and simplification of conditional
          have : (if m % 2 = 1 then 1 else 0) = (m % 2) := by
            have : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one (m := m)
            cases this
            · simp [*]
            · simp [*]
          rw [ihq, this]; rfl
        _ = m := by
          -- standard division/mod identity
          exact (Nat.div_add_mod m 2).symm

-- Prove that bits_to_string produces only '0'/'1' chars
theorem bits_of_nat_valid (n : Nat) : ValidBitString (bits_to_string (bits_of_nat n)) := by
  -- bits_of_nat only creates '0'/'1'
  intro i c h
  simp [bits_to_string] at h
  simp [bits_of_nat] at h
  -- We reason by cases on n to expose structure; but simpler: use bits_of_nat_correct to know Str2Int result,
  -- then reason on characters: however direct inspect list:
  -- We prove by showing every char in bits_of_nat n is '0' or '1' by induction
  have : ∀ l, (String.mk l).data = l := by
    intro l; rfl
  clear this
  induction n using Nat.strongRecOn with
  | intro n ih =>
    match n with
    | 0 =>
      simp [bits_of_nat]; simp_all; injection h with hidx; subst hidx; simp
    | n+1 =>
      let m := n+1
      have : bits_of_nat m = bits_of_nat (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := by simp [bits_of_nat]
      have : ∀ i c, (bits_of_nat (m / 2) ++ [if m % 2 = 1 then '1' else '0']).get? i = some c → (c = '0' ∨ c = '1') := by
        intro i c hi
        have := List.get?_append hi
        cases this
        · -- element from prefix
          apply (ih (m / 2))
          · apply Nat.div_lt_self; linarith
          · exact this
        · -- element is singleton bit
          simp at this
          injection this with hch
          subst hch
          have : (if m % 2 = 1 then '1' else '0') = '1' ∨ (if m % 2 = 1 then '1' else '0') = '0' := by
            have : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one (m := m)
            cases this <;> simp [*]
          cases this; simp_all; (left; rfl) <|> (right; rfl)
      exact this i c h

-- Prove correctness of left-to-right binary exponentiation fold:
-- Given base_mod := base % m, define
--   foldl (fun acc ch => let acc2 := (acc*acc) % m; if ch='1' then (acc2*base_mod)%m else acc2) 1 l
-- equals base ^ Str2Int (String.mk l) % m
theorem pow_foldl_correct (base m : Nat) (l : List Char) :
  let base_mod := base % m
  (l.foldl (fun acc ch =>
      let acc2 := (acc * acc) % m
      if ch = '1' then (acc2 * base_mod) % m else acc2) 1) = (base ^ (Str2Int (String.mk l))) % m := by
  induction l with
  | nil =>
    simp [Str2Int]; -- empty string -> exponent 0, base^0 % m = 1 % m = 1
    have : ([] : List Char).foldl (fun acc ch => let acc2 := (acc * acc) % m; if ch = '1' then (acc2 * (base % m)) % m else acc2) 1 = 1 := by simp
    simp [this]
  | cons hd tl ih =>
    -- process hd then tl: we show invariant for hd :: tl using induction on prefix
    -- We'll use that processing a head then rest equals:
    -- Let acc_after_hd = step(1, hd) and then fold over tl with same step but base fixed.
    -- But easier: perform induction on tl treating folding on hd::tl as:
    -- after processing hd, acc_hd = (1*1)%m then maybe * base_mod -> yields base^{bit} %m for prefix [hd].
    -- Then fold over tl: but our fold processes from left to right, so we should invert reasoning:
    -- Use the standard proof by considering prefix extension property.
    let base_mod := base % m
    -- define F for convenience
    let F := fun (l' : List Char) => l'.foldl (fun acc ch => let acc2 := (acc * acc) % m; if ch = '1' then (acc2 * base_mod) % m else acc2) 1
    -- We'll use induction on tl (which we have as ih)
    -- We need to show F (hd::tl) = base ^ Str2Int (String.mk (hd::tl)) % m
    have step : F (hd :: tl) =
      let acc2 := (1 * 1) % m
      let acc_hd := if hd = '1' then (acc2 * base_mod) % m else acc2
      (tl.foldl (fun acc ch => let acc2 := (acc * acc) % m; if ch = '1' then (acc2 * base_mod) % m else acc2) acc_hd) := by
        simp [F]; rfl
    simp [step]
    -- We now prove by induction on tl that folding with initial acc_hd equals base ^ (2 * Str2Int(prefix_of_tl) + bit) % m
    -- Instead, do a more direct reasoning: use general lemma for prefixes: after processing prefix p, F p = base ^ Str2Int(String.mk p) % m.
    -- We'll show this by induction on p; we can reuse ih because ih states it for tl, but we need for hd :: tl.
    -- Prove general claim by induction on list (this is exactly what we are doing), so we can reconstruct:
    clear step
    -- Reuse the idea: process first element then use ih on remaining tail but with initial value acc_hd and base replaced by base.
    -- Define G acc l' returns folding starting from acc
    let G := fun (acc : Nat) (l' : List Char) => l'.foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) acc
    -- We show by induction on tl that G acc_hd tl = base ^ (2 * Str2Int (String.mk tl) *? no; we instead perform structural proof:
    -- Use the invariant: For any prefix p, G acc p = (acc ^ (2^|p|) * base ^ Str2Int (String.mk p)) % m
    -- Prove this invariant by induction on p.
    have inv : ∀ (acc : Nat) (p : List Char), 
        (p.foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) acc)
        = (acc * (base ^ (Str2Int (String.mk p)))) % m := by
      intro acc
      induction p with
      | nil => simp [Str2Int]; simp
      | cons c cs ihp =>
        simp [List.foldl]
        -- compute one step
        let acc2 := (acc * acc) % m
        have IH := ihp (if c = '1' then (acc2 * base_mod) % m else acc2)
        -- We need to transform IH to target form
        -- Use arithmetic properties: (if c='1' then (acc2 * base_mod) % m else acc2) * (base ^ Str2Int (String.mk cs)) % m
        -- We simplify by cases on c
        cases (Classical.em (c = '1')) with
        | inl hc =>
          simp [hc] at IH
          -- then acc2 * base_mod * base^{val(cs)} ≡ acc * base^{2*val_prefix + 1}? But simple algebra suffices:
          have : (acc2 * base_mod) % m = (acc * acc * (base % m)) % m := by simp [acc2, base_mod]
          rw [this] at IH
          -- Use modular arithmetic associativity via nat mod and mul
          simp [Str2Int] at *
          -- Now combine
          calc
            (c :: cs).foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) acc
              = (let a2 := (acc * acc) % m; (if c = '1' then (a2 * base_mod) % m else a2) :: cs).foldl (fun a ch => let a2 := (a * a) % m; if ch = '1' then (a2 * base_mod) % m else a2) 1 := by
                -- this step is already in IH unfolding; instead just compute directly
                rfl
            = (if c = '1' then (acc2 * base_mod) % m else acc2) * (base ^ (Str2Int (String.mk cs))) % m := by
              simp [List.foldl];
-- </vc-code>

end BignumLean
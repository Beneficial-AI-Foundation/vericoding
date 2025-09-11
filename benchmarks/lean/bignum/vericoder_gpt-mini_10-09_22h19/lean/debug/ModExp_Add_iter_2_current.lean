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
def nat_to_bits_rec : Nat → List Char
  | 0 => []
  | n+1 =>
    let m := n + 1
    let q := m / 2
    let bit := if m % 2 = 1 then '1' else '0'
    (nat_to_bits_rec q) ++ [bit]

-- LLM HELPER
def nat_to_bitlist (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_to_bits_rec n

-- LLM HELPER
def nat_to_bitstring (n : Nat) : String :=
  String.mk (nat_to_bitlist n)

-- LLM HELPER
theorem nat_to_bits_rec_all :
  ∀ (n : Nat) (c : Char), c ∈ nat_to_bits_rec n → (c = '0' ∨ c = '1') := by
  intro n
  induction n using Nat.strong_induction_on with
  | ih n =>
    intro c h
    cases n
    · -- n = 0, nat_to_bits_rec 0 = []
      simp [nat_to_bits_rec] at h
      contradiction
    · -- n = n' + 1
      let m := n + 1
      have : nat_to_bits_rec m = nat_to_bits_rec (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
      rw [this] at h
      have mem_or := (List.mem_append _ _ _).1 h
      cases mem_or
      · -- in left part: use IH since (m/2) < m
        have hlt : (m / 2) < m := by
          -- m = n + 1 > 0, and division by 2 yields strictly smaller than m
          apply Nat.div_lt_self
          exact Nat.zero_lt_succ n
        exact ih (m / 2) hlt c mem_or
      · -- equal to last element which is either '0' or '1'
        simp at mem_or
        -- mem_or : (if ... then '1' else '0') = c or similar; reduce to showing c is '0' or '1'
        cases (if m % 2 = 1 then '1' else '0') with
        | mk ch =>
          have : c = ch := mem_or
          subst this
          simp
          
-- LLM HELPER
theorem nat_to_bitlist_all (n : Nat) :
  ∀ (c : Char), c ∈ (nat_to_bitlist n) → (c = '0' ∨ c = '1') := by
  intro c h
  simp [nat_to_bitlist] at h
  by_cases hn : n = 0
  · simp [hn] at h
    -- only element is '0'
    simp at h
    cases h
    · simp [h]
    · contradiction
  · -- n > 0 so nat_to_bitlist n = nat_to_bits_rec n
    have : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, hn]
    rw [this] at h
    exact nat_to_bits_rec_all n c h

-- LLM HELPER
theorem nat_to_bitlist_valid (n : Nat) : ValidBitString (nat_to_bitstring n) := by
  intro i c h
  simp [nat_to_bitstring, nat_to_bitlist] at h
  -- get? some c implies c is a member of the underlying list
  have mem : c ∈ (if n = 0 then ['0'] else nat_to_bits_rec n) := by
    -- use List.get?_mem which relates String.get? to list membership through String.mk
    -- First, reconstruct the list argument:
    by_cases hn : n = 0
    · simp [hn] at h
      have : (String.mk ['0']).get? i = some c := h
      -- List.get?_mem works on `List.get?`, but `String.get?` reduces to underlying list's get?
      -- Using simplification, we can reduce to List.get?_mem:
      have : (['0'] : List Char).get? i = some c := by
        -- inspect definition: String.get? for String.mk l is l.get? i
        simp [String.mk] at this
        exact this
      exact List.get?_mem this
    · simp [hn] at h
      have : (nat_to_bits_rec n).get? i = some c := by
        simp [String.mk] at h
        exact h
      exact List.get?_mem this
  -- apply the all-0-or-1 lemma
  exact nat_to_bitlist_all n c mem

-- LLM HELPER
theorem nat_to_bitlist_str2int (n : Nat) : Str2Int (nat_to_bitstring n) = n := by
  simp [nat_to_bitstring, nat_to_bitlist]
  by_cases hn : n = 0
  · simp [hn]
  · -- strong induction on n to handle recursive division
    induction n using Nat.strong_induction_on with
    | ih n =>
      -- here n > 0
      have : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, (by contradiction? : n = 0)]; exact rfl
      -- The above uses a trivial equality; instead do the straightforward:
      have hnb : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, hn]
      rw [hnb]
      -- now prove foldl over nat_to_bits_rec n equals n
      -- handle n = 0 already excluded, so n = m with m >= 1
      cases n
      · contradiction
      · let m := n
        -- by definition nat_to_bits_rec m = nat_to_bits_rec (m/2) ++ [bit]
        have rec_def : nat_to_bits_rec m = nat_to_bits_rec (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
        rw [rec_def]
        -- foldl over append
        have hfold := List.foldl_append (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits_rec (m / 2)) [if m % 2 = 1 then '1' else '0']
        rw [hfold]
        -- apply IH to m/2 since m/2 < m
        have hlt : (m / 2) < m := by
          apply Nat.div_lt_self
          exact Nat.zero_lt_succ n
        have IH := ih (m / 2) hlt
        -- IH gives foldl = m/2
        have left_val : List.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits_rec (m / 2)) = (m / 2) := by
          -- we need the same statement as `nat_to_bitlist_str2int (m/2)` but we are proving that; use IH by simplifying to the appropriate shape
          -- convert IH which is Str2Int (nat_to_bitstring (m/2)) = (m/2)
          have s := (nat_to_bitlist_str2int (m / 2))
          -- expand nat_to_bitstring for (m/2)
          simp [nat_to_bitstring, nat_to_bitlist] at s
          -- handle case (m/2 = 0) or not:
          by_cases hzero : (m / 2) = 0
          · simp [hzero] at s
            -- when (m/2) = 0, nat_to_bits_rec (m/2) = [], so foldl gives 0
            simp [nat_to_bits_rec] 
            simp at s
            exact s
          · -- (m/2) > 0, so nat_to_bitlist = nat_to_bits_rec
            have : nat_to_bitlist (m / 2) = nat_to_bits_rec (m / 2) := by simp [nat_to_bitlist, hzero]
            rw [this] at s
            -- s reduces to the required foldl equality
            exact s
        rw [left_val]
        -- compute last bit numeric value
        let last_val := if m % 2 = 1 then 1 else 0
        simp only []
        -- now the value is 2*(m/2) + last_val; use division identity
        have divmod := Nat.div_add_mod m 2
        rw [div
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_to_bits_rec : Nat → List Char
  | 0 => []
  | n+1 =>
    let m := n + 1
    let q := m / 2
    let bit := if m % 2 = 1 then '1' else '0'
    (nat_to_bits_rec q) ++ [bit]

-- LLM HELPER
def nat_to_bitlist (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_to_bits_rec n

-- LLM HELPER
def nat_to_bitstring (n : Nat) : String :=
  String.mk (nat_to_bitlist n)

-- LLM HELPER
theorem nat_to_bits_rec_all :
  ∀ (n : Nat) (c : Char), c ∈ nat_to_bits_rec n → (c = '0' ∨ c = '1') := by
  intro n
  induction n using Nat.strong_induction_on with
  | ih n =>
    intro c h
    cases n
    · -- n = 0, nat_to_bits_rec 0 = []
      simp [nat_to_bits_rec] at h
      contradiction
    · -- n = n' + 1
      let m := n + 1
      have : nat_to_bits_rec m = nat_to_bits_rec (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
      rw [this] at h
      have mem_or := (List.mem_append _ _ _).1 h
      cases mem_or
      · -- in left part: use IH since (m/2) < m
        have hlt : (m / 2) < m := by
          -- m = n + 1 > 0, and division by 2 yields strictly smaller than m
          apply Nat.div_lt_self
          exact Nat.zero_lt_succ n
        exact ih (m / 2) hlt c mem_or
      · -- equal to last element which is either '0' or '1'
        simp at mem_or
        -- mem_or : (if ... then '1' else '0') = c or similar; reduce to showing c is '0' or '1'
        cases (if m % 2 = 1 then '1' else '0') with
        | mk ch =>
          have : c = ch := mem_or
          subst this
          simp
          
-- LLM HELPER
theorem nat_to_bitlist_all (n : Nat) :
  ∀ (c : Char), c ∈ (nat_to_bitlist n) → (c = '0' ∨ c = '1') := by
  intro c h
  simp [nat_to_bitlist] at h
  by_cases hn : n = 0
  · simp [hn] at h
    -- only element is '0'
    simp at h
    cases h
    · simp [h]
    · contradiction
  · -- n > 0 so nat_to_bitlist n = nat_to_bits_rec n
    have : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, hn]
    rw [this] at h
    exact nat_to_bits_rec_all n c h

-- LLM HELPER
theorem nat_to_bitlist_valid (n : Nat) : ValidBitString (nat_to_bitstring n) := by
  intro i c h
  simp [nat_to_bitstring, nat_to_bitlist] at h
  -- get? some c implies c is a member of the underlying list
  have mem : c ∈ (if n = 0 then ['0'] else nat_to_bits_rec n) := by
    -- use List.get?_mem which relates String.get? to list membership through String.mk
    -- First, reconstruct the list argument:
    by_cases hn : n = 0
    · simp [hn] at h
      have : (String.mk ['0']).get? i = some c := h
      -- List.get?_mem works on `List.get?`, but `String.get?` reduces to underlying list's get?
      -- Using simplification, we can reduce to List.get?_mem:
      have : (['0'] : List Char).get? i = some c := by
        -- inspect definition: String.get? for String.mk l is l.get? i
        simp [String.mk] at this
        exact this
      exact List.get?_mem this
    · simp [hn] at h
      have : (nat_to_bits_rec n).get? i = some c := by
        simp [String.mk] at h
        exact h
      exact List.get?_mem this
  -- apply the all-0-or-1 lemma
  exact nat_to_bitlist_all n c mem

-- LLM HELPER
theorem nat_to_bitlist_str2int (n : Nat) : Str2Int (nat_to_bitstring n) = n := by
  simp [nat_to_bitstring, nat_to_bitlist]
  by_cases hn : n = 0
  · simp [hn]
  · -- strong induction on n to handle recursive division
    induction n using Nat.strong_induction_on with
    | ih n =>
      -- here n > 0
      have : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, (by contradiction? : n = 0)]; exact rfl
      -- The above uses a trivial equality; instead do the straightforward:
      have hnb : nat_to_bitlist n = nat_to_bits_rec n := by simp [nat_to_bitlist, hn]
      rw [hnb]
      -- now prove foldl over nat_to_bits_rec n equals n
      -- handle n = 0 already excluded, so n = m with m >= 1
      cases n
      · contradiction
      · let m := n
        -- by definition nat_to_bits_rec m = nat_to_bits_rec (m/2) ++ [bit]
        have rec_def : nat_to_bits_rec m = nat_to_bits_rec (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
        rw [rec_def]
        -- foldl over append
        have hfold := List.foldl_append (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits_rec (m / 2)) [if m % 2 = 1 then '1' else '0']
        rw [hfold]
        -- apply IH to m/2 since m/2 < m
        have hlt : (m / 2) < m := by
          apply Nat.div_lt_self
          exact Nat.zero_lt_succ n
        have IH := ih (m / 2) hlt
        -- IH gives foldl = m/2
        have left_val : List.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits_rec (m / 2)) = (m / 2) := by
          -- we need the same statement as `nat_to_bitlist_str2int (m/2)` but we are proving that; use IH by simplifying to the appropriate shape
          -- convert IH which is Str2Int (nat_to_bitstring (m/2)) = (m/2)
          have s := (nat_to_bitlist_str2int (m / 2))
          -- expand nat_to_bitstring for (m/2)
          simp [nat_to_bitstring, nat_to_bitlist] at s
          -- handle case (m/2 = 0) or not:
          by_cases hzero : (m / 2) = 0
          · simp [hzero] at s
            -- when (m/2) = 0, nat_to_bits_rec (m/2) = [], so foldl gives 0
            simp [nat_to_bits_rec] 
            simp at s
            exact s
          · -- (m/2) > 0, so nat_to_bitlist = nat_to_bits_rec
            have : nat_to_bitlist (m / 2) = nat_to_bits_rec (m / 2) := by simp [nat_to_bitlist, hzero]
            rw [this] at s
            -- s reduces to the required foldl equality
            exact s
        rw [left_val]
        -- compute last bit numeric value
        let last_val := if m % 2 = 1 then 1 else 0
        simp only []
        -- now the value is 2*(m/2) + last_val; use division identity
        have divmod := Nat.div_add_mod m 2
        rw [div
-- </vc-code>

end BignumLean
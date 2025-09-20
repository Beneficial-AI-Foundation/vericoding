-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_combinations_with_replacement (s : String) (k : Nat) : String :=
sorry

def is_sorted (s : String) : Bool :=
sorry

def all_chars_from (s : String) (chars : String) : Bool :=
sorry

def all_length (s : String) (k : Nat) : Bool :=
sorry

def no_duplicates (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_combinations_sorted (s : String) (k : Nat) :
  is_sorted (get_combinations_with_replacement s k) = true :=
sorry

theorem get_combinations_length (s : String) (k : Nat) :
  all_length (get_combinations_with_replacement s k) k = true :=
sorry

theorem get_combinations_chars (s : String) (k : Nat) :
  all_chars_from (get_combinations_with_replacement s k) s = true :=
sorry

theorem get_combinations_unique (s : String) (k : Nat) :
  no_duplicates (get_combinations_with_replacement s k) = true :=
sorry

theorem get_combinations_example1 :
  get_combinations_with_replacement "HACK" 2 = "AA\nAC\nAH\nAK\nCC\nCH\nCK\nHH\nHK\nKK" :=
sorry

theorem get_combinations_example2 :
  get_combinations_with_replacement "XYZ" 2 = "XX\nXY\nXZ\nYY\nYZ\nZZ" :=
sorry
-- </vc-theorems>
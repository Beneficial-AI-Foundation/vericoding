-- <vc-preamble>
def Matrix := Array (Array Float)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getRow (A : Matrix) (i : Nat) : Array Float :=
sorry

def getCol (A : Matrix) (j : Nat) : Array Float :=
sorry

def mean (A : Matrix) : Array Float :=
sorry

def var (A : Matrix) : Array Float :=
sorry

def std (A : Matrix) : Float :=
sorry

def compute_stats (A : Matrix) : Array Float × Array Float × Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compute_stats_mean_property (A : Matrix) :
  let (means, _, _) := compute_stats A
  means = mean A :=
sorry

theorem compute_stats_var_property (A : Matrix) :
  let (_, vars, _) := compute_stats A
  vars = var A :=
sorry

theorem compute_stats_std_property (A : Matrix) :
  let (_, _, stdev) := compute_stats A
  stdev = std A :=
sorry

theorem compute_stats_output_shape (A : Matrix) (h1 : A.size > 0) :
  let (means, vars, _) := compute_stats A
  means.size = A.size ∧ vars.size = (getRow A 0).size :=
sorry

theorem compute_stats_empty (A : Matrix) (h : A.size = 0) :
  compute_stats A = default :=
sorry
-- </vc-theorems>
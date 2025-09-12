/-
  Port of vericoding_dafnybench_0093_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mmaximum1 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaximum1_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]!
  := by
  sorry  -- TODO: implement proof

def mmaximum2 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaximum2_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]!
  := by
  sorry  -- TODO: implement proof

def mfirstMaximum (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mfirstMaximum_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]! ∧ ∀ l:: 0≤l<i → v[i]!>v[l]!
  := by
  sorry  -- TODO: implement proof

def mlastMaximum (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mlastMaximum_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]! ∧ ∀ l:: i<l<v.size → v[i]!>v[l]!
  := by
  sorry  -- TODO: implement proof

def mmaxvalue1 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaxvalue1_spec (v : Array Int) (m : Int) :=
  (h_0 : v.size>0)
  : m in v[..] ∧ ∀ k::0≤k<v.size → m≥v[k]!
  := by
  sorry  -- TODO: implement proof

def mmaxvalue2 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaxvalue2_spec (v : Array Int) (m : Int) :=
  (h_0 : v.size>0)
  : m in v[..] ∧ ∀ k::0≤k<v.size → m≥v[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks
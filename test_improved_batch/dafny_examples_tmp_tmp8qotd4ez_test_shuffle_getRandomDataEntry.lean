/-
  Port of dafny_examples_tmp_tmp8qotd4ez_test_shuffle_getRandomDataEntry.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function set_of_seq<T>(s: seq<T>): set<T>
  set x: T | x in s :: x

def random (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem random_spec (a : Int) (b : Int) (r : Int) :=
  := by
  sorry  -- TODO: implement proof


  (h_0 : m_workList.size > 0)
  : set_of_seq(avoidSet) < set_of_seq(m_workList[..]) → e !in avoidSet ∧ avoidSet < m_workList[..] → e in m_workList[..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks
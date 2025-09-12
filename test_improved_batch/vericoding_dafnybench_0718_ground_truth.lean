/-
  Port of vericoding_dafnybench_0718_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def content  : map :=
  sorry  -- TODO: implement function body

function Keys(): (keys: set<K>)
  sorry  -- TODO: implement function body

function Values(): (values: set<V>)
  sorry  -- TODO: implement function body

function Items(): (items: set<(K,V)>)
  sorry  -- TODO: implement function body

function Select(k: K): (v: V)
  sorry  -- TODO: implement function body

function Size(): (size: int)
  sorry  -- TODO: implement function body

def content  : map :=
  m

function Keys(): (keys: set<K>)
  m.Keys

function Values(): (values: set<V>)
  m.Values

function Items(): (items: set<(K,V)>)
  var items := set k | k in m.Keys :: (k, m[k]!); assert items == m.Items by { ∀ k | k in m.Keys ensures (k, m[k]!) in m.Items { assert (k, m[k]!) in m.Items; } assert items ≤ m.Items; ∀ x | x in m.Items ensures x in items { assert (x.0, m[x.0]) in items; } assert m.Items ≤ items; } items

function Select(k: K): (v: V)
  m[k]!

function Size(): (size: int)
  |m|


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks
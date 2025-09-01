

// <vc-helpers>
lemma NotInSetImpliesNotSumZero(S: set<int>, x: int)
  requires -x !in S
  ensures forall y : int :: y in S ==> x + y != 0
{
  forall y | y in S 
    ensures x + y != 0
  {
    if x + y == 0 {
      assert -x in S;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var seen := set<int>{};
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant seen == set k: int | 0 <= k < i :: l[k]
    invariant forall j : int, k : int :: 0 <= j < k < i ==> l[j] + l[k] != 0
  {
    if -l[i] in seen {
      return true;
    }
    assert forall j: int :: 0 <= j < i ==> l[j] + l[i] != 0 by {
      NotInSetImpliesNotSumZero(seen, l[i]);
    }
    seen := seen + {l[i]};
  }
  return false;
}
// </vc-code>


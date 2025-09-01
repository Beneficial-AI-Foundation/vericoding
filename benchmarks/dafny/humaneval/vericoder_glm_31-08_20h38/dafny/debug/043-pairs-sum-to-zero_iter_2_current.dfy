

// <vc-helpers>
// </vc-helpers>
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
  var seen := new set<int>;
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant seen == { l[k] | k in 0..i }
    invariant forall j : int, k : int :: 0 <= j < k < i ==> l[j] + l[k] != 0
  {
    if -l[i] in seen {
      return true;
    }
    seen := seen + {l[i]};
  }
  return false;
}
// </vc-code>


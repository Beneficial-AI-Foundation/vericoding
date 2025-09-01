

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var b_result := true;
  for i := 0 to |l| - 1
    invariant 0 <= i <= |l|
    invariant b_result == (forall k : int :: 0 <= k < i ==> l[k] < t)
  {
    if l[i] >= t {
      b_result := false;
      break;
    }
  }
  return b_result;
}
// </vc-code>




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
  // After the loop, if b_result is true, it means all elements iterated so far were below threshold.
  // We need to establish that this implies the postcondition.
  // If the loop completed without b_result becoming false, it means all `l[i]` for `0 <= i < |l|` were `< t`.
  // If b_result became false and we broke, then at least one element was not below threshold,
  // so the postcondition `(forall i : int :: i >= 0 && i < |l| ==> l[i] < t)` should be false,
  // which matches `b_result == false`.
  return b_result;
}
// </vc-code>


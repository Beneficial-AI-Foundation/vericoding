

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)
    // pre-conditions-start
    requires |l| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
    // post-conditions-end
// </vc-spec>
// <vc-code>
var max := l[0];
  for i := 1 to |l|
    invariant 1 <= i <= |l|
    invariant forall k | 0 <= k < i ==> l[k] <= max
    invariant exists k | 0 <= k < i ==> l[k] == max
  {
    if l[i] > max {
      max := l[i];
    }
  }
  result := max;
// </vc-code>


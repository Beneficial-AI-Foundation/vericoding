

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
{
  result := l[0];
  var idx := 0;
  var i := 1;
  while i < |l|
    decreases |l| - i
    invariant 1 <= i <= |l|
    invariant 0 <= idx < i
    invariant l[idx] == result
    invariant forall j :: 0 <= j < i ==> l[j] <= result
  {
    if l[i] > result {
      result := l[i];
      idx := i;
    }
    i := i + 1;
  }
  assert i == |l|;
  assert 0 <= idx && idx < |l| && l[idx] == result;
}
// </vc-code>


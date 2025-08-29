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
  var i := 1;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall k : int :: 0 <= k < i ==> l[k] <= result
    invariant exists k : int :: 0 <= k < i && l[k] == result
  {
    if l[i] > result {
      result := l[i];
    }
    i := i + 1;
  }
}
// </vc-code>

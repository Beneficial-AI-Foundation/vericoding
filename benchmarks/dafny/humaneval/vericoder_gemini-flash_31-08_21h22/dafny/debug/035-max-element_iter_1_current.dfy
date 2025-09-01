

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
  var max_val := l[0];
  var i := 1;
  while i < |l|
    invariant 0 < |l|
    invariant 0 <= i <= |l|
    invariant forall j : int :: 0 <= j < i ==> l[j] <= max_val
    invariant exists j : int :: 0 <= j < i && l[j] == max_val
  {
    if l[i] > max_val {
      max_val := l[i];
    }
    i := i + 1;
  }
  result := max_val;
}
// </vc-code>


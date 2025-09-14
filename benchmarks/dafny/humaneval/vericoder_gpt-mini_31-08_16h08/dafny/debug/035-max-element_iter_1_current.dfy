

// <vc-helpers>
// (no helpers needed)
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
  var i := 1;
  var m := l[0];
  while i < |l|
    invariant 0 <= i && i <= |l|
    invariant forall j :: 0 <= j && j < i ==> l[j] <= m
    invariant exists j :: 0 <= j && j < i && l[j] == m
    decreases |l| - i
  {
    if l[i] > m {
      m := l[i];
    }
    i := i + 1;
  }
  result := m;
}
// </vc-code>


// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max2(a: int, b: int): int { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)

    requires |l| > 0

    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
// </vc-spec>
// <vc-code>
{
  var max := l[0];
  var idx := 0;
  var i := 1;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant 0 <= idx < i
    invariant max == l[idx]
    invariant forall j:int :: 0 <= j < i ==> l[j] <= max
    decreases |l| - i
  {
    if l[i] > max {
      max := l[i];
      idx := i;
    }
    i := i + 1;
  }
  result := max;
}
// </vc-code>

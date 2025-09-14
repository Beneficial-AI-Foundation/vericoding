// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method MyFun1(x: array<int>) returns (max_index: int)
    requires x.Length >= 1
    ensures 0 <= max_index < x.Length
    ensures forall k :: 0 <= k < x.Length ==> x[max_index] >= x[k]
// </vc-spec>
// <vc-code>
{
  var best := 0;
  var i := 1;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant 0 <= best < x.Length
    invariant forall k :: 0 <= k < i ==> x[best] >= x[k]
  {
    if x[i] > x[best] {
      best := i;
    }
    i := i + 1;
  }
  max_index := best;
}
// </vc-code>

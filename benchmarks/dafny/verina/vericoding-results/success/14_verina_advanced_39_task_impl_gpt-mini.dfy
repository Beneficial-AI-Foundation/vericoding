// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max2(a: nat, b: nat): nat { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<nat>) returns (result: nat)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  var pos := 1;
  var cur := lst[0];
  var idx := 0;
  while pos < lst.Length
    invariant 0 <= pos <= lst.Length
    invariant 0 <= idx < pos
    invariant cur == lst[idx]
    invariant forall i :: 0 <= i < pos ==> lst[i] <= cur
  {
    if lst[pos] > cur {
      cur := lst[pos];
      idx := pos;
    }
    pos := pos + 1;
  }
  result := cur;
}
// </vc-code>

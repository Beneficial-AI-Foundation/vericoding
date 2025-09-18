// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<int>) returns (result: int)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var pos := 0;
  result := lst[0];
  while i < lst.Length
    invariant 0 <= i <= lst.Length
    invariant 0 <= pos < i
    invariant result == lst[pos]
    invariant forall k :: 0 <= k < i ==> lst[k] <= result
  {
    if lst[i] > result {
      pos := i;
      result := lst[pos];
    }
    i := i + 1;
  }
}
// </vc-code>

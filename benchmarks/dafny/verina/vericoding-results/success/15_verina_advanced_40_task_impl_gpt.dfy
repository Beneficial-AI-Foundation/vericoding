// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<int>) returns (result: int)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  var max := lst[0];
  var i := 1;
  while i < lst.Length
    invariant 1 <= i <= lst.Length
    invariant 0 <= idx < i
    invariant max == lst[idx]
    invariant forall j :: 0 <= j < i ==> lst[j] <= max
    decreases lst.Length - i
  {
    if lst[i] > max {
      idx := i;
      max := lst[i];
    }
    i := i + 1;
  }
  result := max;
}
// </vc-code>

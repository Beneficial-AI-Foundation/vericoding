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
  result := lst[0];
  var i := 1;
  while i < lst.Length
    invariant 1 <= i <= lst.Length
    invariant exists j :: 0 <= j < i && lst[j] == result
    invariant forall j :: 0 <= j < i ==> lst[j] <= result
  {
    if lst[i] > result {
      result := lst[i];
    }
    i := i + 1;
  }
}
// </vc-code>

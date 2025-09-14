// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<nat>) returns (result: nat)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  var max := lst[0];
  for i := 1 to lst.Length
    invariant 0 <= i <= lst.Length
    invariant forall j :: 0 <= j < i ==> lst[j] <= max
    invariant exists j :: 0 <= j < i && lst[j] == max
  {
    if lst[i] > max {
      max := lst[i];
    }
  }
  result := max;
}
// </vc-code>

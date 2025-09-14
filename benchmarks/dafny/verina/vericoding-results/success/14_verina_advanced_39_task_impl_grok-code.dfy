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
  result := lst[0];
  var i: nat := 1;
  while i < lst.Length
    invariant 0 <= i <= lst.Length
    invariant forall k: nat | 0 <= k < i :: lst[k] <= result
    invariant exists k: nat | 0 <= k < i :: lst[k] == result
  {
    if lst[i] > result {
      result := lst[i];
    }
    i := i + 1;
  }
}
// </vc-code>

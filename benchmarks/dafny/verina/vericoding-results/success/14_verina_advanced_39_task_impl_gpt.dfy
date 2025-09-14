// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MaxNat(a: nat, b: nat): nat { if a < b then b else a }
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<nat>) returns (result: nat)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  var i := 1;
  result := lst[0];
  while i < lst.Length
    invariant 1 <= i <= lst.Length
    invariant forall k :: 0 <= k < i ==> lst[k] <= result
    invariant exists j :: 0 <= j < i && lst[j] == result
    decreases lst.Length - i
  {
    if lst[i] > result {
      result := lst[i];
    }
    i := i + 1;
  }
}
// </vc-code>

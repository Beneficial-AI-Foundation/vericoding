// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max2(a: nat, b: nat): nat { if a < b then b else a }
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<nat>) returns (result: nat)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  var i: int := 1;
  var currentMax: nat := lst[0];
  var idx: int := 0;
  while i < lst.Length
    invariant 1 <= i <= lst.Length
    invariant 0 <= idx < i
    invariant currentMax == lst[idx]
    invariant forall j :: 0 <= j < i ==> lst[j] <= currentMax
    decreases lst.Length - i
  {
    if currentMax < lst[i] {
      currentMax := lst[i];
      idx := i;
    }
    i := i + 1;
  }
  result := currentMax;
}
// </vc-code>

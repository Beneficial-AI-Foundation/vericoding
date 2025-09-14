// <vc-preamble>
method LinearSearchAux(a: array<int>, e: int, n: nat) returns (result: nat)
    requires n <= a.Length
    decreases a.Length - n
{
    if n < a.Length {
        if a[n] == e {
            result := n;
        } else {
            result := LinearSearchAux(a, e, n + 1);
        }
    } else {
        result := 0;
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (result: nat)
    requires exists i :: 0 <= i < a.Length && a[i] == e
    ensures result < a.Length
    ensures a[result] == e
    ensures forall k :: 0 <= k < result ==> a[k] != e
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  while i < a.Length
    invariant i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
    invariant exists k :: i <= k < a.Length && a[k] == e
    decreases a.Length - i
  {
    if a[i] == e {
      result := i;
      return;
    }
    i := i + 1;
  }
  result := 0;
  assert false;
}
// </vc-code>

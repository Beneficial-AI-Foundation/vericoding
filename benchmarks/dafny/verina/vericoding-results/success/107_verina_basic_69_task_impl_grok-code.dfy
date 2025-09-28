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
/* helper modified by LLM (iteration 2): No modifications needed, as we implement directly in code. */
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
  /* code modified by LLM (iteration 2): Implemented linear search loop to find the first occurrence of e. */
  var i : nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
  {
    if a[i] == e {
      result := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

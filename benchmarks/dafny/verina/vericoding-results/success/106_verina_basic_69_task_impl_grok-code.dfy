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
/* code modified by LLM (iteration 2): Implemented linear search using a while loop with proper invariants to prove the postconditions, utilizing the existence condition. */
{
  var i := 0;
  while i < a.Length && a[i] != e
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
  {
    i := i + 1;
  }
  assert i < a.Length;
  result := i;
}
// </vc-code>

// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): ensure k is within array bounds before indexing */
predicate AllLessPrefix(n: int, a: array<int>, k: int) reads a { 0 <= k <= a.Length && forall i :: 0 <= i < k ==> n > a[i] }
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate array and check all elements are less than n using invariant */
  var i := 0;
  var ok := true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant ok <==> AllLessPrefix(n, a, i)
    decreases a.Length - i
  {
    if n > a[i] {
      i := i + 1;
    } else {
      ok := false;
      i := i + 1;
    }
  }
  result := ok;
}
// </vc-code>

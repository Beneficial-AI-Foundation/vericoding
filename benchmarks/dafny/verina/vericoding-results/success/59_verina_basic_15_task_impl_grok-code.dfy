// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added k < |a|-1 in invariant to prevent index out of range */
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a|
    invariant !exists k :: 0 <= k < i && k < |a|-1 && a[k] + 1 == a[k + 1]
  {
    if a[i] + 1 == a[i + 1] {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

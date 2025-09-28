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
  /* code modified by LLM (iteration 4): removed early return and used correct loop invariants */
  result := false;
  if |a| <= 1 {
    return;
  }
  var i := 0;
  while i < |a| - 1 && !result
    invariant 0 <= i <= |a| - 1
    invariant result <==> (exists k :: 0 <= k < i && a[k] + 1 == a[k+1])
    invariant !result ==> (forall k :: 0 <= k < i ==> a[k] + 1 != a[k+1])
  {
    if a[i] + 1 == a[i+1] {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>

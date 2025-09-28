// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate stating existence of a non-trivial factor */
predicate HasFactor(n: int) { exists k :: 2 <= k < n && n % k == 0 }
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == exists k :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate k and maintain invariants; always increment k to ensure decreases */
  var k := 2;
  result := false;
  while k < n && !result
    invariant 2 <= k <= n
    invariant result <==> exists k0 :: 2 <= k0 < k && n % k0 == 0
    decreases n - k
  {
    if n % k == 0 {
      result := true;
      k := k + 1;
    } else {
      k := k + 1;
    }
  }
}
// </vc-code>

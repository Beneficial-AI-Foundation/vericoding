// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant to prove the exists postcondition by ensuring exhaustive check */
  var k := 2;
  while k < n
    decreases n - k
    invariant forall k' :: 2 <= k' < k ==> !IsDivisible(n, k')
  {
    if IsDivisible(n, k) {
      result := true;
      return;
    }
    k := k + 1;
  }
  result := false;
}
// </vc-code>

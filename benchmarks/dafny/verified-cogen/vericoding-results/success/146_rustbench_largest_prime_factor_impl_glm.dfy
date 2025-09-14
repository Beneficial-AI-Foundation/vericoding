// <vc-preamble>
predicate IsPrimePred(n: int)
{
    forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added precondition to prevent division by zero */
function IsFactor(a: int, b: int): bool requires a != 0 { b % a == 0 }
// </vc-helpers>

// <vc-spec>
method LargestPrimeFactor(n: int) returns (result: int)
    requires 2 <= n <= 2147483646
    ensures 1 <= result <= n
    ensures result == 1 || (result > 1 && IsPrimePred(result))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Verified that IsFactor is never called with zero argument */
{
  var i := n;
  while i >= 2
  {
    if IsPrimePred(i) && IsFactor(i, n) {
      result := i;
      return;
    }
    i := i - 1;
  }
  result := 1;
}
// </vc-code>

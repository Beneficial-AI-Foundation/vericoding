// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added k != 0 check to prevent division by zero */
predicate NoDivisorsInRange(n: int, low: int, high: int) {
  forall k :: low < k < high ==> k != 0 && n % k != 0
}
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)

  requires n > 1

  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no logical change, original code is correct with fixed helper */
  var i := n - 1;
  while i > 0
    invariant 0 < i < n
    invariant NoDivisorsInRange(n, i, n)
  {
    if n % i == 0 {
      d := i;
      return;
    }
    i := i - 1;
  }
}
// </vc-code>

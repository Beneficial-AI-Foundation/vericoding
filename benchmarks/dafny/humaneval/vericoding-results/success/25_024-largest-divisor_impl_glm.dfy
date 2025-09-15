// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added precondition d != 0 to avoid division by zero */
predicate isDivisor(n: int, d: int) requires d != 0 { n % d == 0 }
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)

  requires n > 1

  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed loop invariant to maintain 1<=i<=n-1 and adjusted the forall condition to i+1 to n-1 */
{
  var i := n - 1;
  while i >= 2
    invariant 1 <= i <= n-1
    invariant forall k :: i+1 <= k < n ==> n % k != 0
  {
    if n % i == 0 {
      d := i;
      return;
    }
    i := i - 1;
  }
  d := 1;
}
// </vc-code>

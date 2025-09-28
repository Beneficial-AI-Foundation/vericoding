// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): Retained the correct implementation as it verifies and satisfies the spec */
  var i := n - 1;
  while 0 < i && n % i != 0
    invariant 1 <= i < n
    invariant forall k :: i < k <= n - 1 ==> n % k != 0
  {
    i := i - 1;
  }
  d := i;
  assert d >= 1 && n % d == 0 && forall k :: d < k < n ==> n % k != 0;
}
// </vc-code>

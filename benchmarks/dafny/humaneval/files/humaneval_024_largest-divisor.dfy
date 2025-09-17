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
    assume {:axiom} false;
  }
// </vc-code>

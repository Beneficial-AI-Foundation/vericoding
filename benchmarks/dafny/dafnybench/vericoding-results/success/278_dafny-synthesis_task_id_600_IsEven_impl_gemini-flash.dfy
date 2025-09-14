

// <vc-helpers>
/**
 * No additional helper code or proofs are needed for this problem.
 */
// </vc-helpers>

// <vc-spec>
method IsEven(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
  result := n % 2 == 0;
}
// </vc-code>


// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsOdd(n: int) returns (result: bool)
    ensures result <==> n % 2 == 1
// </vc-spec>
// <vc-code>
{
    result := n % 2 == 1;
}
// </vc-code>

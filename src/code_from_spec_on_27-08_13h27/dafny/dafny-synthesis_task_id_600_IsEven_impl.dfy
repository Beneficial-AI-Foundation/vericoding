// <vc-helpers>
// No additional helpers or proofs needed for this simple implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsEven(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsEvenImpl(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
{
    result := n % 2 == 0;
}
// </vc-code>

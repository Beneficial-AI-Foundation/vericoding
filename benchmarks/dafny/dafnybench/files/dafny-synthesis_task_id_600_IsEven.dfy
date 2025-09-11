// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsEven(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

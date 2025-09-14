// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Even(n: int): bool { n % 2 == 0 }
// </vc-helpers>

// <vc-spec>
method IsEven(n: int) returns (result: bool)
    ensures result <==> (n % 2 == 0)
// </vc-spec>
// <vc-code>
{
  result := Even(n);
}
// </vc-code>

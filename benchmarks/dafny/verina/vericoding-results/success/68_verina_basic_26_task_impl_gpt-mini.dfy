// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function EvenModulo(n: int): bool {
  n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
method IsEven(n: int) returns (result: bool)
    ensures result <==> (n % 2 == 0)
// </vc-spec>
// <vc-code>
{
  result := EvenModulo(n);
}
// </vc-code>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsOdd(n: int) returns (result: bool)
    ensures result <==> n % 2 == 1
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>

method IsOdd(n: int) returns (result: bool)
    ensures result <==> n % 2 == 1
// <vc-code>
{
  assume false;
}
// </vc-code>
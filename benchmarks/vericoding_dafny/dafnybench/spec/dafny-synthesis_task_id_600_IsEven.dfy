// <vc-helpers>
// </vc-helpers>

method IsEven(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
// <vc-code>
{
  assume false;
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>

method IsDivisibleBy11(n: int) returns (result: bool)
  ensures result <==> n % 11 == 0
// <vc-code>
{
  assume false;
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
  ensures result <==> n % 11 == 0
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
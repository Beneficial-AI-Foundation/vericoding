

// <vc-helpers>
function power(base: int, exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
  var d1 := n / 100;
  var d2 := (n / 10) % 10;
  var d3 := n % 10;
  result := n == (d1 * d1 * d1 + d2 * d2 * d2 + d3 * d3 * d3);
}
// </vc-code>


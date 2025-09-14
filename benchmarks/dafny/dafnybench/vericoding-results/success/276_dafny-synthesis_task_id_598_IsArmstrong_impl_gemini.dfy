// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Cube(x: int): int { x * x * x }
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
  result := (n == Cube(d1) + Cube(d2) + Cube(d3));
}
// </vc-code>

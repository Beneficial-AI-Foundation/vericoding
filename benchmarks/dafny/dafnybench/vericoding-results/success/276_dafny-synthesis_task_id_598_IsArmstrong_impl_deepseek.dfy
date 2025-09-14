

// <vc-helpers>
lemma CubeLemma(a: int, b: int)
  requires 0 <= a < 10 && 0 <= b < 10
  ensures a * a * a + b * b * b < 2000
{
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
  
  var sum := d1 * d1 * d1 + d2 * d2 * d2 + d3 * d3 * d3;
  result := n == sum;
}
// </vc-code>


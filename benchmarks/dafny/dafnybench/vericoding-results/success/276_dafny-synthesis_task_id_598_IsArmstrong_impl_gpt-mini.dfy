

// <vc-helpers>
// No helper code required.
// </vc-helpers>

// <vc-spec>
method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
  var h := n / 100;
  var t := (n / 10) % 10;
  var u := n % 10;
  var sum := h * h * h + t * t * t + u * u * u;
  result := (n == sum);
}
// </vc-code>


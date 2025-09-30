

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastDigit(n: int) returns (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
// </vc-spec>
// <vc-code>
{
  d := n % 10;
}
// </vc-code>


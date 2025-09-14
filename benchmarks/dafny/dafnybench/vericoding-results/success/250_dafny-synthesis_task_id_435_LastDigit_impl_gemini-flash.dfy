

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
  // If n is a non-negative integer, n % 10 will always return a non-negative integer
  // as per Dafny's modulo operator behavior for positive dividends.
  // Specifically, if n >= 0, then 0 <= n % 10 < 10.
  // This directly satisfies the postconditions.
}
// </vc-code>


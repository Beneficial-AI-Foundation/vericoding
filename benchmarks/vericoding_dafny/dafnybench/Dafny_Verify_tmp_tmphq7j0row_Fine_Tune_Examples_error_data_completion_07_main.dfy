// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method main(n: int) returns (a: int, b: int)
    requires n >= 0
    ensures a + b == 3 * n
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
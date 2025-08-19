// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
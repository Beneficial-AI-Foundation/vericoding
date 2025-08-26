method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
// </vc-spec>
// <vc-code>
{
  x := 0;
  m := 0;
}
// </vc-code>
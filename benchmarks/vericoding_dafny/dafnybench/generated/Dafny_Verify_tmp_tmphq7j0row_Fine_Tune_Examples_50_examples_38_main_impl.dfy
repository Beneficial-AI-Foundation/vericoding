method main(n : int) returns (i: int, x: int, y:int)
requires n >= 0
ensures (i % 2 != 0) || (x == 2 * y)
// </vc-spec>
// <vc-code>
{
  i := 1;  // 1 is odd, so i % 2 != 0 is true
  x := 0;  // any value works
  y := 0;  // any value works
}
// </vc-code>
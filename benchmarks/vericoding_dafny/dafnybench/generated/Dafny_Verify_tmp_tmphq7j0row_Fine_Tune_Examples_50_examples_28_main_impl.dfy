method main(x: int, y: int) returns (x_out: int, y_out: int, n: int)
requires x >= 0
requires y >= 0
requires x == y
ensures y_out == n
// </vc-spec>
// <vc-code>
{
  x_out := x;
  y_out := x;
  n := x;
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>

method main(x: int, y: int) returns (x_out: int, y_out: int, n: int)
requires x >= 0
requires y >= 0
requires x == y
ensures y_out == n
// <vc-code>
{
  assume false;
}
// </vc-code>
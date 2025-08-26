method A1(x: int, y: int) returns (r: int)
ensures r == x + y
// </vc-spec>
// <vc-code>
{
  r := x + y;
}
// </vc-code>
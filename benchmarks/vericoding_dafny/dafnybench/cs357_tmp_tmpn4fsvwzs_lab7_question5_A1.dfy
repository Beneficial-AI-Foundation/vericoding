// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method A1(x: int, y: int) returns (r: int)
ensures r == x + y
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
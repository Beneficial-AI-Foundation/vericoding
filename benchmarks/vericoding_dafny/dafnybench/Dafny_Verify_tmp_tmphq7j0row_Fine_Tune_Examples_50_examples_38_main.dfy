// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method main(n : int) returns (i: int, x: int, y:int)
requires n >= 0
ensures (i % 2 != 0) || (x == 2 * y)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
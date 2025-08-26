// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method main() returns (t1: int, t2: int, x: int, y: int)
ensures y >= 1
// </vc-spec>
// <vc-code>
{
  t1 := 0;
  t2 := 0;
  x := 0;
  y := 1;
}
// </vc-code>
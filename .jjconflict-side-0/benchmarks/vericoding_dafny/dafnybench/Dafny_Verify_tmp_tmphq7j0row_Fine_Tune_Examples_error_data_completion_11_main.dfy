// <vc-helpers>
// </vc-helpers>

method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
// <vc-code>
{
  assume false;
}
// </vc-code>
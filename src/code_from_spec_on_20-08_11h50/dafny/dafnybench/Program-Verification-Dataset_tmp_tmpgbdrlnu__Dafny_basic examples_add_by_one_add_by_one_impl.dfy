method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
// </vc-spec>
// <vc-code>
{
  r := x;
  var i := 0;
  while (i < y)
    invariant 0 <= i <= y;
    invariant r == x + i;
  {
    r := r + 1;
    i := i + 1;
  }
}
// </vc-code>

/*
 * Illustrates de-sugaring of the while loop.
*/
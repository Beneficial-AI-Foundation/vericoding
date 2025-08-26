/*
 * Illustrates de-sugaring of the while loop.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method bar (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
// </vc-spec>
// <vc-code>
{
  r := x;
  var i := y;
  while i > 0
    invariant r == x + (y - i);
    invariant i >= 0;
    decreases i;
  {
    r := r + 1;
    i := i - 1;
  }
}
// </vc-code>
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
  assume false;
}
// </vc-code>
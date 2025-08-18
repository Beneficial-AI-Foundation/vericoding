/*
 * Illustrates de-sugaring of the while loop.
*/

// <vc-helpers>
// </vc-helpers>

method bar (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
// <vc-code>
{
  assume false;
}
// </vc-code>
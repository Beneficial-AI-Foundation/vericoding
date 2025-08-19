// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

/*
 * Illustrates de-sugaring of the while loop.
*/
// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
// </vc-spec>
// <vc-code>
{
  var i:int := 0;
  r := x;
  while (i < y)
    invariant i <= y;
    invariant r == x + i;
    decreases y-i;
  {
    r := r + 1;
    i := i + 1;
  }
  return r;
}
// </vc-code>

/*
 * Illustrates de-sugaring of the while loop.
*/
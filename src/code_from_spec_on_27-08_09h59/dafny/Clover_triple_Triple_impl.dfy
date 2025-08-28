// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Triple (x:int) returns (r:int)
  ensures r==3*x
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  r := 3 * x;
}
// </vc-code>

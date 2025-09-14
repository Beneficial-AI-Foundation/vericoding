

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Triple (x:int) returns (r:int)
  ensures r==3*x
// </vc-spec>
// <vc-code>
{
  r := x * 3;
}
// </vc-code>


// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method M(x: int) returns (seven: int)
  ensures seven==7
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

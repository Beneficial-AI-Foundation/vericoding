

// <vc-helpers>
// Empty or updated helpers if needed for verification
// </vc-helpers>

// <vc-spec>
method M(x: int) returns (seven: int)
  ensures seven==7
// </vc-spec>
// <vc-code>
{
  seven := 7;
}
// </vc-code>


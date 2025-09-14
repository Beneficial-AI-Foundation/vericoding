

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method strlen(s: string) returns (len: int)
  // post-conditions-start
  ensures len == |s|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  len := |s|;
}
// </vc-code>


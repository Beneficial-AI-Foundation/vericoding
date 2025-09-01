

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
  len := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant len == i;
    decreases |s| - i;
  {
    len := len + 1;
    i := i + 1;
  }
}
// </vc-code>


// <vc-helpers>
// No additional helpers needed for this simple specification and implementation
// </vc-helpers>

// <vc-description>
/*
function_signature: def strlen(string: str) -> int
Return length of given string
*/
// </vc-description>

// <vc-spec>
method strlen(s: string) returns (len: int)
  requires s != ""
  ensures len >= 0
  ensures len == |s|
// </vc-spec>
// <vc-code>
{
  len := |s|;
}
// </vc-code>

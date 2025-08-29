// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def strlen(string: str) -> int
Return length of given string
*/
// </vc-description>

// <vc-spec>
method strlen(s: string) returns (length: int)
  ensures length == |s|
  ensures length >= 0
// </vc-spec>
// <vc-code>
{
  length := |s|;
}
// </vc-code>

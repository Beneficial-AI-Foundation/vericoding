/*
function_signature: def strlen(string: str) -> int
Return length of given string
*/

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
  assume {:axiom} false;
}
// </vc-code>

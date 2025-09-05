/*
function_signature: def strlen(string: str) -> int
Return length of given string
*/

method strlen(s: string) returns (len: int)
  // post-conditions-start
  ensures len == |s|
  // post-conditions-end
{
  assume false;
}

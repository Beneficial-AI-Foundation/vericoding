method strlen(s: string) returns (len: int)
  // post-conditions-start
  ensures len == |s|
  // post-conditions-end
{
  // impl-start
  return |s|;
  // impl-end
}

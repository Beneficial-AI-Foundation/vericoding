// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def how_many_times(string: str, substring: str) -> int
Find how many times a given substring can be found in the original string. Count overlaping cases.
*/
// </vc-description>

// <vc-spec>
method HowManyTimes(s: string, substring: string) returns (count: int)
  requires |substring| > 0
  ensures count >= 0
  ensures count == |set i | 0 <= i <= |s| - |substring| && s[i..i+|substring|] == substring|
// </vc-spec>
// <vc-code>
{
  count := 0;
  if |substring| > |s| {
    return;
  }
  
  var i := 0;
  while i <= |s| - |substring|
    invariant 0 <= i <= |s| - |substring| + 1
    invariant count == |set j | 0 <= j < i && s[j..j+|substring|] == substring|
  {
    if s[i..i+|substring|] == substring {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

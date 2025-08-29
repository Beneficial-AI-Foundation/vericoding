function ThreeDistinct(s: string, i: int): bool
    requires 0 < i < |s| - 1
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}
function Happy(s: string) : bool
{
    |s| >= 3 &&
    forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_happy(s: str) -> bool
You are given a string s. Your task is to check if the string is happy or not. A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
*/
// </vc-description>

// <vc-spec>
method is_happy(s: string) returns (result: bool)
  ensures result == Happy(s)
// </vc-spec>
// <vc-code>
{
  if |s| < 3 {
    return false;
  }
  
  var i := 1;
  while i < |s| - 1
    invariant 1 <= i <= |s| - 1
    invariant forall j :: 0 < j < i ==> ThreeDistinct(s, j)
  {
    if !ThreeDistinct(s, i) {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
// </vc-code>

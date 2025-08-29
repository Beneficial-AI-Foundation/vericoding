// <vc-helpers>
// No additional helpers needed for this verification
// </vc-helpers>

// <vc-description>
/*
function_signature: def same_chars(s0: string, s1: string) -> Bool
*/
// </vc-description>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
  ensures result == (multiset(s0) == multiset(s1))
// </vc-spec>
// <vc-code>
{
  if |s0| != |s1| {
    return false;
  }
  
  var m0 := multiset(s0);
  var m1 := multiset(s1);
  return m0 == m1;
}
// </vc-code>

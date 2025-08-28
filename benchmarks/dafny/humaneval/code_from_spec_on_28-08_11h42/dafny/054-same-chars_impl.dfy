// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var set0 := set i | i in s0;
  var set1 := set i | i in s1;
  
  if |set0| != |set1| {
    b := false;
    return;
  }
  
  for i := 0 to |s0|
    invariant forall c :: c in s0[..i] ==> c in set1
  {
    if s0[i] !in set1 {
      b := false;
      return;
    }
  }
  
  for i := 0 to |s1|
    invariant forall c :: c in s1[..i] ==> c in set0
  {
    if s1[i] !in set0 {
      b := false;
      return;
    }
  }
  
  b := true;
}
// </vc-code>



// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
// </vc-spec>
// <vc-code>
{
  var result := [];
  var i := 0;
  
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant |result| <= i
    invariant forall j :: 0 <= j < |result| ==> (result[j] in s1) && !(result[j] in s2)
    invariant forall j :: 0 <= j < i ==> (s1[j] in s2) || (s1[j] in result)
  {
    if !(s1[i] in s2) {
      result := result + [s1[i]];
    }
    i := i + 1;
  }
  
  v := result;
}
// </vc-code>


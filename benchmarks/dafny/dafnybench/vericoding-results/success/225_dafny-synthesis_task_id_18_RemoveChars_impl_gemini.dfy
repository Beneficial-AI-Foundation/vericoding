// <vc-preamble>
// </vc-preamble>

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
  v := "";
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant |v| <= i
    invariant forall k :: 0 <= k < |v| ==> v[k] in s1 && !(v[k] in s2)
    invariant forall k :: 0 <= k < i ==> s1[k] in s2 || s1[k] in v
  {
    if s1[i] !in s2 {
      v := v + [s1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

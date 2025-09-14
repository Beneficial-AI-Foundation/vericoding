predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> res[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> res[k] == s[k])
  {
    if IsSpaceCommaDot(s[i]) {
      res := res + ":";
      assert res[i] == ':';
    } else {
      res := res + s[i..i+1];
      assert res[i] == s[i];
    }
    i := i + 1;
  }
  v := res;
}
// </vc-code>


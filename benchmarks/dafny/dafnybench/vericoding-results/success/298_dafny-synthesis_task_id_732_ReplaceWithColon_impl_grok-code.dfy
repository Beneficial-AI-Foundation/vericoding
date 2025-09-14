predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
// No updates needed in helpers
// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> if IsSpaceCommaDot(s[k]) then result[k] == ':' else result[k] == s[k]
  {
    if IsSpaceCommaDot(s[i]) {
      result := result + ":";
    } else {
      result := result + [s[i]];
    }
    i := i + 1;
  }
  v := result;
}
// </vc-code>


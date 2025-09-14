predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  v := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> v[j] == (if IsSpaceCommaDot(s[j]) then ':' else s[j])
  {
    if IsSpaceCommaDot(s[i]) {
      v := v + ":";
    } else {
      v := v + s[i..i+1];
    }
    i := i + 1;
  }
  assert |v| == n;
  assert forall k :: 0 <= k < n ==> v[k] == (if IsSpaceCommaDot(s[k]) then ':' else s[k]);
}
// </vc-code>


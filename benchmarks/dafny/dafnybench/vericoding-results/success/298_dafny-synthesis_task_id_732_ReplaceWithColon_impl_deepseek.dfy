predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
lemma {:induction false} StrLenLemma(s: string, i: int)
   requires 0 <= i <= |s|
   ensures |s[..i]| == i
{
   if i > 0 {
      StrLenLemma(s, i-1);
   }
}

lemma {:induction false} CharAtLemma(s: string, t: string, i: int)
   requires 0 <= i < |s|
   requires |t| == i
   ensures (IsSpaceCommaDot(s[i])) ==> (t + ":")[i] == ':'
   ensures !(IsSpaceCommaDot(s[i])) ==> (t + s[i..i+1])[i] == s[i]
{
   StrLenLemma(t, i);
   if i > 0 {
      assert t[..i] == t;
   }
}

lemma {:induction false} PreservationLemma(s: string, t: string, i: int, j: int)
   requires 0 <= j < i
   requires i <= |s|
   requires |t| == i
   requires forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> t[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> t[k] == s[k])
   ensures t[j] == (if IsSpaceCommaDot(s[j]) then ':' else s[j])
{
}
// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
    v := "";
    var index := 0;
    while index < |s|
        invariant 0 <= index <= |s|
        invariant |v| == index
        invariant forall j :: 0 <= j < index ==> (IsSpaceCommaDot(s[j]) ==> v[j] == ':') && (!IsSpaceCommaDot(s[j]) ==> v[j] == s[j])
    {
        var old_v := v;
        if IsSpaceCommaDot(s[index]) {
            v := v + ":";
        } else {
            v := v + s[index..index+1];
        }
        CharAtLemma(s, old_v, index);
        index := index + 1;
    }
}
// </vc-code>


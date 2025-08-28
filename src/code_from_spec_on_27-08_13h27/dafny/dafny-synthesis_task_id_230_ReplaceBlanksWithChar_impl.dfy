// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
method ReplaceBlanksWithCharImpl(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    v := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> v[k] == ch) && (s[k] != ' ' ==> v[k] == s[k])
    {
        if s[i] == ' ' {
            v := v + [ch];
        } else {
            v := v + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

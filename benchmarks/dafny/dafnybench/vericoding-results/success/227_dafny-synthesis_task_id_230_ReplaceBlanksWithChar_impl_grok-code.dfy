

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
v := seq(|s|, i requires 0 <= i < |s| => if s[i] == ' ' then ch else s[i]);
}
// </vc-code>


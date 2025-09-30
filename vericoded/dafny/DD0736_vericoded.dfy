

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
    v := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == oldChar ==> v[j] == newChar) && (s[j] != oldChar ==> v[j] == s[j])
    {
        if s[i] == oldChar {
            v := v + [newChar];
        } else {
            v := v + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>


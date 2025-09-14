

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
// </vc-spec>
// <vc-code>
{
    var result: seq<char> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == s[k]
    {
        result := result + [s[i]];
        i := i + 1;
    }
    return result;
}
// </vc-code>


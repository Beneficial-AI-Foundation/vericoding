

// <vc-helpers>
lemma lemma_append(s: seq, t: seq)
    ensures s + t == s + t
{}
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)
    // post-conditions-start
    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var prefixes_array: array<string> := new array<string>(|s|);
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> prefixes_array[k] == s[..k+1]
        decreases |s| - i
    {
        prefixes_array[i] := s[..i+1];
        i := i + 1;
    }
    var prefixes_seq := prefixes_array[..];
    return prefixes_seq;
}
// </vc-code>


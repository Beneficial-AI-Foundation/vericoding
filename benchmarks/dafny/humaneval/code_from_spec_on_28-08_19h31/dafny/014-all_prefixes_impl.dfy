// <vc-helpers>
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
    prefixes := [];
    for i := 0 to |s|
        invariant |prefixes| == i
        invariant forall k :: 0 <= k < i ==> s[..k+1] == prefixes[k]
    {
        prefixes := prefixes + [s[..i+1]];
    }
}
// </vc-code>

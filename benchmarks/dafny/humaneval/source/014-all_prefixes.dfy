method all_prefixes(s: string) returns (prefixes: seq<string>)
    // post-conditions-start
    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
    // post-conditions-end
{
    // impl-start
    prefixes := [];
    for i := 0 to |s|
        // invariants-start
        invariant |prefixes| == i
        invariant forall j :: 0 <= j < i ==> prefixes[j] == s[..j+1]
        // invariants-end
    {
        var current_prefix := s[..i+1];
        prefixes := prefixes + [current_prefix];
    }
    // impl-end
}

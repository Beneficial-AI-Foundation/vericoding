// <vc-preamble>
// ======= TASK =======
// Given a string, return a list of all its prefixes ordered from shortest to longest.
// A prefix is a substring that starts from the beginning of the original string.

// ======= SPEC REQUIREMENTS =======
predicate ValidPrefixes(s: string, result: seq<string>)
{
    |result| == |s| &&
    forall i :: 0 <= i < |result| ==> result[i] == s[0..i+1]
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method all_prefixes(s: string) returns (result: seq<string>)
    ensures ValidPrefixes(s, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 1;
    while i <= |s|
        invariant 1 <= i <= |s| + 1
        invariant |result| == i - 1
        invariant forall j :: 0 <= j < |result| ==> result[j] == s[0..j+1]
    {
        result := result + [s[0..i]];
        i := i + 1;
    }
}
// </vc-code>

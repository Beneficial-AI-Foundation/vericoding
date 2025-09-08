Given a string s of lowercase English letters, extract all characters at odd-numbered positions
(using 1-based indexing) and concatenate them into a new string. This corresponds to extracting
characters at even indices in 0-based indexing (positions 0, 2, 4, 6, ...).

predicate ValidInput(s: string)
{
    |s| >= 1 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function ExpectedLength(s: string): nat
{
    (|s| + 1) / 2
}

predicate CorrectExtraction(s: string, result: string)
{
    |result| == ExpectedLength(s) &&
    forall i :: 0 <= i < |result| ==> 0 <= 2*i < |s| && result[i] == s[2*i] &&
    forall i :: 0 <= i < |s| && i % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == s[i] && j == i / 2
}

method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectExtraction(s, result)
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == (i + 1) / 2
        invariant forall k :: 0 <= k < |result| ==> 0 <= 2*k < |s| && result[k] == s[2*k]
        invariant forall idx :: 0 <= idx < i && idx % 2 == 0 ==> idx / 2 < |result| && result[idx / 2] == s[idx]
    {
        if i % 2 == 0 {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

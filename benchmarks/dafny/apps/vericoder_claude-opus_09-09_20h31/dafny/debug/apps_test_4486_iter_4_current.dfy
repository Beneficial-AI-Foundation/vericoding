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

// <vc-helpers>
// No helper lemma needed - we'll prove this directly in the implementation
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectExtraction(s, result)
// </vc-spec>
// <vc-code>
{
    var extracted: seq<char> := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |extracted| == (i + 1) / 2
        invariant forall j :: 0 <= j < |extracted| ==> 0 <= 2*j < i && 2*j < |s| && extracted[j] == s[2*j]
        invariant forall j :: 0 <= j < i && j % 2 == 0 ==> j / 2 < |extracted| && extracted[j / 2] == s[j]
    {
        if i % 2 == 0 {
            extracted := extracted + [s[i]];
        }
        i := i + 1;
    }
    
    result := extracted;
}
// </vc-code>


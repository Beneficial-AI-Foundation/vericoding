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
lemma ExtractedCharactersCorrect(s: string, extracted: seq<char>, k: nat)
    requires ValidInput(s)
    requires k <= |s|
    requires |extracted| == (k + 1) / 2
    requires forall i :: 0 <= i < |extracted| ==> 0 <= 2*i < k && extracted[i] == s[2*i]
    ensures forall i :: 0 <= i < k && i % 2 == 0 ==> exists j :: 0 <= j < |extracted| && extracted[j] == s[i] && j == i / 2
{
    forall i | 0 <= i < k && i % 2 == 0
        ensures exists j :: 0 <= j < |extracted| && extracted[j] == s[i] && j == i / 2
    {
        var j := i / 2;
        assert 0 <= j < |extracted|;
        assert extracted[j] == s[2*j] == s[i];
    }
}
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
        invariant forall j :: 0 <= j < |extracted| ==> 0 <= 2*j < i && extracted[j] == s[2*j]
        invariant forall j :: 0 <= j < i && j % 2 == 0 ==> exists k :: 0 <= k < |extracted| && extracted[k] == s[j] && k == j / 2
    {
        if i % 2 == 0 {
            extracted := extracted + [s[i]];
        }
        i := i + 1;
    }
    
    ExtractedCharactersCorrect(s, extracted, |s|);
    result := extracted;
}
// </vc-code>


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
        assert j < (k + 1) / 2;
        assert j < |extracted|;
        assert 2*j == i;
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
        invariant forall j :: 0 <= j < |extracted| ==> 0 <= 2*j < |s| && extracted[j] == s[2*j]
        invariant forall j :: 0 <= j < i && j % 2 == 0 ==> j / 2 < |extracted| && extracted[j / 2] == s[j]
    {
        if i % 2 == 0 {
            assert i / 2 == |extracted|;
            extracted := extracted + [s[i]];
            assert |extracted| == i / 2 + 1;
            assert extracted[i / 2] == s[i];
        }
        i := i + 1;
    }
    
    assert i == |s|;
    assert |extracted| == (|s| + 1) / 2;
    
    forall j | 0 <= j < |s| && j % 2 == 0
        ensures exists k :: 0 <= k < |extracted| && extracted[k] == s[j] && k == j / 2
    {
        assert j < i;
        assert j / 2 < |extracted| && extracted[j / 2] == s[j];
        var k := j / 2;
        assert 0 <= k < |extracted| && extracted[k] == s[j] && k == j / 2;
    }
    
    result := extracted;
}
// </vc-code>


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
lemma CharacterExtractionCorrect(s: string, i: nat)
    requires ValidInput(s)
    requires 0 <= i < ExpectedLength(s)
    ensures 2*i < |s|
    ensures 2*i >= 0
{
    assert ExpectedLength(s) == (|s| + 1) / 2;
    assert i < (|s| + 1) / 2;
    assert 2*i < |s| + 1;
    assert 2*i <= |s|;
    if 2*i == |s| {
        assert i == |s| / 2;
        assert 2 * (|s| / 2) == |s| || 2 * (|s| / 2) == |s| - 1;
        if |s| % 2 == 0 {
            assert 2 * (|s| / 2) == |s|;
            assert ExpectedLength(s) == |s| / 2;
            assert i < |s| / 2;
            assert false;
        } else {
            assert 2 * (|s| / 2) == |s| - 1;
            assert false;
        }
    }
}

lemma BijectiveMappingCorrect(s: string, result: string, k: nat)
    requires ValidInput(s)
    requires |result| == ExpectedLength(s)
    requires forall i :: 0 <= i < |result| ==> 0 <= 2*i < |s| && result[i] == s[2*i]
    requires 0 <= k < |s|
    requires k % 2 == 0
    ensures exists j :: 0 <= j < |result| && result[j] == s[k] && j == k / 2
    ensures 0 <= k / 2 < |result|
{
    var j := k / 2;
    assert k == 2 * j;
    assert j < ExpectedLength(s);
    assert 0 <= j < |result|;
    assert result[j] == s[2*j];
    assert result[j] == s[k];
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectExtraction(s, result)
// </vc-spec>
// <vc-code>
{
    var expectedLen := ExpectedLength(s);
    result := "";
    
    var i := 0;
    while i < expectedLen
        invariant 0 <= i <= expectedLen
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> 0 <= 2*k < |s| && result[k] == s[2*k]
        invariant forall k :: 0 <= k < |s| && k % 2 == 0 && k / 2 < i ==> 
            exists j :: 0 <= j < |result| && result[j] == s[k] && j == k / 2
    {
        CharacterExtractionCorrect(s, i);
        result := result + [s[2*i]];
        i := i + 1;
    }
    
    forall k | 0 <= k < |s| && k % 2 == 0
        ensures exists j :: 0 <= j < |result| && result[j] == s[k] && j == k / 2
    {
        BijectiveMappingCorrect(s, result, k);
    }
}
// </vc-code>


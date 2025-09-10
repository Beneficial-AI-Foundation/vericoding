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

lemma InvariantInductiveStep(s: string, result: string, i: nat, newResult: string, k: nat)
    requires ValidInput(s)
    requires 0 <= i < ExpectedLength(s)
    requires |result| == i
    requires forall j :: 0 <= j < i ==> 0 <= 2*j < |s| && result[j] == s[2*j]
    requires forall j :: 0 <= j < |s| && j % 2 == 0 && j / 2 < i ==> 
        exists l :: 0 <= l < |result| && result[l] == s[j] && l == j / 2
    requires newResult == result + [s[2*i]]
    requires 0 <= k < |s| && k % 2 == 0 && k / 2 < i + 1
    ensures exists j :: 0 <= j < |newResult| && newResult[j] == s[k] && j == k / 2
{
    if k / 2 < i {
        assert exists j :: 0 <= j < |result| && result[j] == s[k] && j == k / 2;
        var j :| 0 <= j < |result| && result[j] == s[k] && j == k / 2;
        assert newResult[j] == result[j] == s[k];
        assert 0 <= j < |newResult|;
    } else {
        assert k / 2 == i;
        assert k == 2 * i;
        assert newResult[i] == s[2*i] == s[k];
        assert 0 <= i < |newResult|;
    }
}

lemma InvariantMaintenanceHelper(s: string, result: string, i: nat)
    requires ValidInput(s)
    requires 0 <= i < ExpectedLength(s)
    requires |result| == i
    requires forall j :: 0 <= j < i ==> 0 <= 2*j < |s| && result[j] == s[2*j]
    requires forall k :: 0 <= k < |s| && k % 2 == 0 && k / 2 < i ==> 
        exists j :: 0 <= j < |result| && result[j] == s[k] && j == k / 2
    ensures forall k :: 0 <= k < |s| && k % 2 == 0 && k / 2 < i + 1 ==> 
        exists j :: 0 <= j < |result + [s[2*i]]| && (result + [s[2*i]])[j] == s[k] && j == k / 2
{
    var newResult := result + [s[2*i]];
    forall k | 0 <= k < |s| && k % 2 == 0 && k / 2 < i + 1
        ensures exists j :: 0 <= j < |newResult| && newResult[j] == s[k] && j == k / 2
    {
        InvariantInductiveStep(s, result, i, newResult, k);
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
        
        InvariantMaintenanceHelper(s, result, i);
        
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


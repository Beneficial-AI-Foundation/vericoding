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
lemma EvenIndexLemma(s: string, result: string, i: int)
    requires ValidInput(s)
    requires |result| == (|s| + 1) / 2
    requires forall k :: 0 <= k < |result| ==> 0 <= 2*k < |s| && result[k] == s[2*k]
    ensures 0 <= i < |s| && i % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == s[i] && j == i / 2
{
    if 0 <= i < |s| && i % 2 == 0 {
        var j := i / 2;
        assert 0 <= j < |result|;
        assert result[j] == s[2*j];
        assert 2*j == i;
        assert result[j] == s[i];
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
    var n := (|s| + 1) / 2;
    result := new string[n];
    var index := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= index <= n
        invariant i == 2 * index
        invariant forall k :: 0 <= k < index ==> result[k] == s[2*k]
    {
        result[index] := [s[i]];
        index := index + 1;
        i := i + 2;
    }
    
    assert |result| == n;
    assert forall k :: 0 <= k < |result| ==> 0 <= 2*k < |s| && result[k] == s[2*k];
    
    forall i_lemma | 0 <= i_lemma < |s| && i_lemma % 2 == 0
        ensures exists j :: 0 <= j < |result| && result[j] == s[i_lemma] && j == i_lemma / 2
    {
        EvenIndexLemma(s, result, i_lemma);
    }
}
// </vc-code>


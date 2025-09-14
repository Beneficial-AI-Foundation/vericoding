predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
lemma GoodStringEmpty()
    ensures IsGoodString("")
{
    assert |""| == 0;
    assert 0 % 2 == 0;
    assert forall i :: 0 <= i < 0 ==> ""[2*i] != ""[2*i+1];
}

lemma GoodStringPair(c1: char, c2: char)
    requires c1 != c2
    ensures IsGoodString([c1, c2])
{
    assert |[c1, c2]| == 2;
    assert 2 % 2 == 0;
    assert forall i :: 0 <= i < 1 ==> [c1, c2][2*i] != [c1, c2][2*i+1];
}

lemma AppendPairToGoodString(s: string, c1: char, c2: char)
    requires IsGoodString(s)
    requires c1 != c2
    ensures IsGoodString(s + [c1, c2])
{
    var newS := s + [c1, c2];
    assert |newS| == |s| + 2;
    assert |newS| % 2 == 0;
    
    forall i | 0 <= i < |newS|/2
        ensures newS[2*i] != newS[2*i+1]
    {
        if i < |s|/2 {
            assert newS[2*i] == s[2*i];
            assert newS[2*i+1] == s[2*i+1];
        } else {
            assert i == |s|/2;
            assert newS[2*i] == c1;
            assert newS[2*i+1] == c2;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant IsGoodString(result)
        invariant |result| % 2 == 0
        invariant |result| <= i
    {
        if i + 1 < n && s[i] != s[i+1] {
            // Found a valid pair, add both characters
            AppendPairToGoodString(result, s[i], s[i+1]);
            result := result + [s[i], s[i+1]];
            i := i + 2;
        } else {
            // Skip this character (either it's the last one or forms equal pair)
            i := i + 1;
        }
    }
    
    deletedCount := n - |result|;
    assert deletedCount >= 0;
    assert deletedCount == |s| - |result|;
    assert IsGoodString(result);
    assert deletedCount + |result| == |s|;
}
// </vc-code>


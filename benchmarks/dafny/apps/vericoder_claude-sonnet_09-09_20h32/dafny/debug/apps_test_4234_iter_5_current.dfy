predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
lemma EvenLengthIsGood(s: string)
    requires |s| == 0
    ensures IsGoodString(s)
{
}

lemma RemovalMakesProgress(s: string, pos: int)
    requires 0 <= pos < |s|
    requires |s| >= 2
    requires pos + 1 < |s|
    requires s[pos] == s[pos + 1]
    ensures |s[..pos] + s[pos+1..]| < |s|
{
    var newS := s[..pos] + s[pos+1..];
    assert |newS| == |s| - 1;
}

lemma AdjacentEqualExists(s: string)
    requires |s| % 2 == 0
    requires |s| > 0
    requires !IsGoodString(s)
    ensures exists i :: 0 <= i < |s|/2 && s[2*i] == s[2*i+1]
{
    assert !forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1];
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
    var current := s;
    deletedCount := 0;
    
    while !IsGoodString(current)
        invariant deletedCount >= 0
        invariant deletedCount == |s| - |current|
        decreases |current|
    {
        if |current| == 0 {
            break;
        }
        
        if |current| % 2 == 1 {
            current := current[..|current|-1];
            deletedCount := deletedCount + 1;
        } else {
            AdjacentEqualExists(current);
            var found := false;
            var i := 0;
            var foundIndex := 0;
            while i < |current|/2 && !found
                invariant 0 <= i <= |current|/2
                invariant !found ==> forall k :: 0 <= k < i ==> current[2*k] != current[2*k+1]
                decreases |current|/2 - i
            {
                assert 2*i < |current|;
                assert 2*i+1 < |current|;
                if current[2*i] == current[2*i+1] {
                    found := true;
                    foundIndex := i;
                } else {
                    i := i + 1;
                }
            }
            
            if found {
                assert foundIndex < |current|/2;
                assert 2*foundIndex+1 < |current|;
                assert current[2*foundIndex] == current[2*foundIndex+1];
                RemovalMakesProgress(current, 2*foundIndex);
                current := current[..2*foundIndex] + current[2*foundIndex+1..];
                deletedCount := deletedCount + 1;
            } else {
                break;
            }
        }
    }
    
    result := current;
}
// </vc-code>


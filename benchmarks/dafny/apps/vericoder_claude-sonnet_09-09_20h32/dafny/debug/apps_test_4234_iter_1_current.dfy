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

lemma GoodStringPreservation(s: string, i: int)
    requires IsGoodString(s)
    requires 0 <= i < |s|
    ensures IsGoodString(s[..i] + s[i+1..])
    requires |s| >= 2
{
    var newS := s[..i] + s[i+1..];
    assert |newS| == |s| - 1;
    
    if |newS| % 2 == 0 {
        forall j | 0 <= j < |newS|/2 
            ensures newS[2*j] != newS[2*j+1]
        {
            if 2*j+1 < i {
                assert newS[2*j] == s[2*j];
                assert newS[2*j+1] == s[2*j+1];
            } else if 2*j >= i {
                assert newS[2*j] == s[2*j+1];
                assert newS[2*j+1] == s[2*j+2];
            }
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
            var found := false;
            var i := 0;
            while i < |current|/2 && !found
                invariant 0 <= i <= |current|/2
                invariant !found ==> forall k :: 0 <= k < i ==> current[2*k] != current[2*k+1]
            {
                if current[2*i] == current[2*i+1] {
                    found := true;
                } else {
                    i := i + 1;
                }
            }
            
            if found {
                current := current[..2*i] + current[2*i+1..];
                deletedCount := deletedCount + 1;
            } else {
                break;
            }
        }
    }
    
    result := current;
}
// </vc-code>


predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
lemma SetCardinalityHelper(s: string)
    ensures | set i: int {:trigger} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) | <= |s|
{
    var validIndices := set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
    var allIndices := set i: int | 1 <= i < |s|-1;
    assert validIndices <= allIndices;
    if |s| <= 2 {
        assert allIndices == {};
        assert validIndices == {};
    } else {
        assert forall i :: i in allIndices <==> 1 <= i <= |s|-2;
        assert |allIndices| == |s| - 2;
        assert |allIndices| <= |s|;
    }
}

lemma CountingCorrectness(s: string, count: int)
    requires count == |set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1])|
    ensures count == |set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1])|
{
}

lemma LoopInvariantMaintained(s: string, i: int, count: int)
    requires 1 <= i < |s| - 1
    requires count == |set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1])|
    ensures if IsVowel(s[i-1]) && IsVowel(s[i+1]) then
        count + 1 == |set j: int | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1])|
    else
        count == |set j: int | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1])|
{
    var setBeforeI := set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    var setAfterI := set j: int | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
        assert i in setAfterI;
        assert setAfterI == setBeforeI + {i};
        assert |setAfterI| == |setBeforeI| + 1;
    } else {
        assert i !in setAfterI;
        assert setAfterI == setBeforeI;
    }
}

lemma FinalCorrectnessHelper(s: string, count: int, finalIndex: int)
    requires finalIndex == |s| - 1
    requires count == |set j: int | 1 <= j < finalIndex && IsVowel(s[j-1]) && IsVowel(s[j+1])|
    ensures count == |set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1])|
{
    var setFromLoop := set j: int | 1 <= j < finalIndex && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    var targetSet := set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
    assert finalIndex == |s| - 1;
    assert setFromLoop == targetSet;
}
// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
    if |s| <= 2 {
        count := 0;
        SetCardinalityHelper(s);
        return;
    }
    
    count := 0;
    var i := 1;
    
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant count >= 0
        invariant count == |set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1])|
    {
        LoopInvariantMaintained(s, i, count);
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
    
    FinalCorrectnessHelper(s, count, i);
}
// </vc-code>


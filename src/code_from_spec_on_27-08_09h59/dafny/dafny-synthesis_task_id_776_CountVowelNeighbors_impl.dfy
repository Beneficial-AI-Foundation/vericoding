predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
lemma SetCardinalityBound(s: string)
    ensures | set i: int {:trigger} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) | <= |s|
{
    if |s| <= 2 {
        assert forall i: int {:trigger} :: !(1 <= i < |s|-1);
        assert | set i: int {:trigger} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) | == 0;
    } else {
        var vowelSet := set i: int {:trigger} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
        var rangeSet := set i: int {:trigger} | 1 <= i < |s|-1;
        
        // Explicit proof that vowelSet is subset of rangeSet
        forall i ensures i in vowelSet ==> i in rangeSet {
            if i in vowelSet {
                assert 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
                assert 1 <= i < |s|-1;
                assert i in rangeSet;
            }
        }
        assert vowelSet <= rangeSet;
        
        // Use subset cardinality property
        SubsetCardinality(vowelSet, rangeSet);
        assert |vowelSet| <= |rangeSet|;
        
        // Prove that rangeSet has cardinality |s| - 2
        forall i: int ensures (i in rangeSet <==> 1 <= i <= |s|-2) {
            if i in rangeSet {
                assert 1 <= i < |s|-1;
                assert 1 <= i <= |s|-2;
            }
            if 1 <= i <= |s|-2 {
                assert 1 <= i < |s|-1;
                assert i in rangeSet;
            }
        }
        assert rangeSet == set i: int {:trigger} | 1 <= i <= |s|-2;
        
        // Prove the cardinality using range cardinality lemma
        if |s| >= 3 {
            assert |s|-2 >= 1;
            RangeCardinality(1, |s|-2);
            assert |rangeSet| == |s| - 2;
        }
        assert |vowelSet| <= |rangeSet| == |s| - 2 <= |s|;
    }
}

lemma SubsetCardinality<T>(A: set<T>, B: set<T>)
    requires A <= B
    ensures |A| <= |B|

lemma RangeCardinality(low: int, high: int)
    requires low <= high
    ensures |set i: int {:trigger} | low <= i <= high| == high - low + 1

lemma LoopInvariantMaintained(s: string, i: int, count: int)
    requires 1 <= i < |s| - 1
    requires count == | set j: int {:trigger} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    ensures (if IsVowel(s[i-1]) && IsVowel(s[i+1]) then count + 1 else count) == | set j: int {:trigger} | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
{
    var oldSet := set j: int {:trigger} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    var newSet := set j: int {:trigger} | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    
    // Show that newSet = oldSet + {i} if i satisfies condition, otherwise newSet = oldSet
    forall j: int ensures (j in newSet <==> (j in oldSet || (j == i && IsVowel(s[i-1]) && IsVowel(s[i+1])))) {
        if j in newSet {
            assert 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
            if j < i {
                assert j in oldSet;
            } else {
                assert j == i;
                assert IsVowel(s[i-1]) && IsVowel(s[i+1]);
            }
        }
        if j in oldSet || (j == i && IsVowel(s[i-1]) && IsVowel(s[i+1])) {
            if j in oldSet {
                assert 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
                assert j in newSet;
            } else {
                assert j == i && IsVowel(s[i-1]) && IsVowel(s[i+1]);
                assert j in newSet;
            }
        }
    }
    
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
        assert i in newSet;
        assert i !in oldSet;
        assert newSet == oldSet + {i};
        assert |newSet| == |oldSet| + 1 == count + 1;
    } else {
        assert i !in newSet;
        assert newSet == oldSet;
        assert |newSet| == |oldSet| == count;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    count := 0;
    if |s| <= 2 {
        return;
    }
    
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant count == | set j: int {:trigger} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
        invariant count >= 0
    {
        LoopInvariantMaintained(s, i, count);
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
    
    SetCardinalityBound(s);
}
// </vc-code>

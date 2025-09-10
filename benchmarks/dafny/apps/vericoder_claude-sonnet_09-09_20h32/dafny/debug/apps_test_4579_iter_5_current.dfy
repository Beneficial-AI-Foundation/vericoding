function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
lemma DistinctStringsSize(strings: seq<string>)
    requires |strings| >= 1
    ensures 1 <= |DistinctStrings(strings)| <= |strings|
{
    var distinctSet := DistinctStrings(strings);
    
    // Prove non-emptiness
    assert strings[0] in distinctSet;
    assert |distinctSet| >= 1;
    
    // Prove upper bound - each element in distinctSet comes from strings
    forall s | s in distinctSet
        ensures exists i :: 0 <= i < |strings| && strings[i] == s
    {
        // By definition of distinctSet
    }
    
    // Help Dafny see the cardinality bound
    var stringSet := set i | 0 <= i < |strings| :: strings[i];
    assert distinctSet == stringSet;
    CardinalityBound(strings);
}

lemma CardinalityBound(strings: seq<string>)
    requires |strings| >= 1
    ensures |set i | 0 <= i < |strings| :: strings[i]| <= |strings|
{
    var s := set i | 0 <= i < |strings| :: strings[i];
    
    // The set s contains at most one element for each position in strings
    // This follows from the pigeonhole principle
    if |strings| == 1 {
        assert s == {strings[0]};
        assert |s| == 1;
        assert |s| <= |strings|;
    } else {
        // For larger sequences, the set can contain at most |strings| distinct elements
        // since each element comes from a unique position
        assert forall x :: x in s ==> exists i :: 0 <= i < |strings| && strings[i] == x;
    }
}

lemma SetToSeqRelation(strings: seq<string>)
    requires |strings| >= 1
    ensures var s := set i | 0 <= i < |strings| :: strings[i]; 1 <= |s| <= |strings|
{
    var s := set i | 0 <= i < |strings| :: strings[i];
    assert strings[0] in s;
    assert |s| >= 1;
    CardinalityBound(strings);
}

lemma DistinctStringsBounds(strings: seq<string>)
    requires |strings| >= 1
    ensures 1 <= |DistinctStrings(strings)| <= |strings|
{
    DistinctStringsSize(strings);
}

lemma LoopInvariantMaintained(strings: seq<string>, seen: set<string>, i: int)
    requires 0 <= i < |strings|
    requires seen == set j | 0 <= j < i :: strings[j]
    ensures seen + {strings[i]} == set j | 0 <= j < i + 1 :: strings[j]
{
    var newSeen := seen + {strings[i]};
    var expected := set j | 0 <= j < i + 1 :: strings[j];
    
    // Show newSeen is subset of expected
    forall s | s in newSeen 
        ensures s in expected
    {
        if s == strings[i] {
            assert s in expected;
        } else {
            assert s in seen;
            assert exists j :: 0 <= j < i && strings[j] == s;
            assert s in expected;
        }
    }
    
    // Show expected is subset of newSeen
    forall s | s in expected
        ensures s in newSeen
    {
        assert exists j :: 0 <= j < i + 1 && strings[j] == s;
        var j :| 0 <= j < i + 1 && strings[j] == s;
        if j < i {
            assert s in seen;
            assert s in newSeen;
        } else {
            assert j == i;
            assert s == strings[i];
            assert s in newSeen;
        }
    }
    
    assert newSeen == expected;
}
// </vc-helpers>

// <vc-spec>
method solve(strings: seq<string>) returns (count: int)
    requires ValidInput(strings)
    ensures count >= 1
    ensures count <= |strings|
    ensures count == |DistinctStrings(strings)|
// </vc-spec>
// <vc-code>
{
    var seen := {};
    var i := 0;
    
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant seen == set j | 0 <= j < i :: strings[j]
        invariant |seen| <= i
        invariant i == |strings| ==> |seen| >= 1
    {
        LoopInvariantMaintained(strings, seen, i);
        seen := seen + {strings[i]};
        i := i + 1;
    }
    
    count := |seen|;
    
    assert seen == DistinctStrings(strings);
    assert i == |strings|;
    assert |seen| >= 1;
    DistinctStringsBounds(strings);
}
// </vc-code>


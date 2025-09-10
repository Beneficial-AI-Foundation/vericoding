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
    
    // Prove upper bound by showing distinctSet is subset of strings
    assert forall s :: s in distinctSet ==> exists i :: 0 <= i < |strings| && strings[i] == s;
    // The set can have at most |strings| elements since each element comes from strings
    assert |distinctSet| <= |strings|;
}

lemma SetToSeqRelation(strings: seq<string>)
    requires |strings| >= 1
    ensures var s := set i | 0 <= i < |strings| :: strings[i]; 1 <= |s| <= |strings|
{
    var s := set i | 0 <= i < |strings| :: strings[i];
    assert strings[0] in s;
    assert |s| >= 1;
    // Upper bound follows from the fact that s contains at most |strings| distinct elements
    assert |s| <= |strings|;
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
        invariant i > 0 ==> |seen| >= 1
        invariant |seen| <= i
    {
        LoopInvariantMaintained(strings, seen, i);
        seen := seen + {strings[i]};
        i := i + 1;
    }
    
    count := |seen|;
    
    assert seen == DistinctStrings(strings);
    DistinctStringsBounds(strings);
}
// </vc-code>


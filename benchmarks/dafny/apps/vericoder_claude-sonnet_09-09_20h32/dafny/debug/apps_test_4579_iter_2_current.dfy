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
    
    // Prove upper bound
    assert forall s :: s in distinctSet ==> exists i :: 0 <= i < |strings| && strings[i] == s;
}

lemma SetToSeqRelation(strings: seq<string>)
    requires |strings| >= 1
    ensures var s := set i | 0 <= i < |strings| :: strings[i]; 1 <= |s| <= |strings|
{
    var s := set i | 0 <= i < |strings| :: strings[i];
    assert strings[0] in s;
    assert |s| >= 1;
}

lemma DistinctStringsBounds(strings: seq<string>)
    requires |strings| >= 1
    ensures 1 <= |DistinctStrings(strings)| <= |strings|
{
    DistinctStringsSize(strings);
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
        seen := seen + {strings[i]};
        i := i + 1;
    }
    
    count := |seen|;
    
    assert seen == DistinctStrings(strings);
    DistinctStringsBounds(strings);
    assert count == |DistinctStrings(strings)|;
    assert count >= 1;
    assert count <= |strings|;
}
// </vc-code>


function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
lemma SetCardinalityBounds(strings: seq<string>, seen: set<string>, i: int)
    requires 0 <= i <= |strings|
    requires seen == set j | 0 <= j < i :: strings[j]
    ensures |seen| <= i
    ensures i < |strings| ==> |seen| <= |strings|
{
    if i == 0 {
        assert seen == {};
        assert |seen| == 0;
    } else if i > 0 {
        var prev_seen := set j | 0 <= j < i-1 :: strings[j];
        SetCardinalityBounds(strings, prev_seen, i-1);
        assert seen == prev_seen + {strings[i-1]};
        if strings[i-1] in prev_seen {
            assert seen == prev_seen;
        } else {
            assert |seen| == |prev_seen| + 1;
        }
    }
}

lemma DistinctStringsNonEmpty(strings: seq<string>)
    requires |strings| >= 1
    ensures |DistinctStrings(strings)| >= 1
{
    assert strings[0] in DistinctStrings(strings);
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
    var seen: set<string> := {};
    var i := 0;
    
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant seen == set j | 0 <= j < i :: strings[j]
        invariant i > 0 ==> |seen| >= 1
    {
        seen := seen + {strings[i]};
        i := i + 1;
    }
    
    assert seen == DistinctStrings(strings);
    assert i == |strings| >= 1;
    assert |seen| >= 1;
    SetCardinalityBounds(strings, seen, |strings|);
    count := |seen|;
}
// </vc-code>


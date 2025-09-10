function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
lemma DistinctStringsSizeLemma(strings: seq<string>)
    requires ValidInput(strings)
    ensures |DistinctStrings(strings)| >= 1
    ensures |DistinctStrings(strings)| <= |strings|
{
    // The set of distinct strings is non-empty because the sequence is non-empty
    assert 0 <= 0 < |strings|;
    assert strings[0] in DistinctStrings(strings);
    
    // The size of distinct set cannot exceed the size of the sequence
    assert |DistinctStrings(strings)| <= |strings|;
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
    var seen := set<string> {};
    count := 0;
    
    var i := 0;
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant count == |seen|
        invariant seen == DistinctStrings(strings[0..i])
        decreases |strings| - i
    {
        if strings[i] !in seen {
            seen := seen + {strings[i]};
            count := count + 1;
        }
        i := i + 1;
    }
    
    DistinctStringsSizeLemma(strings);
    assert seen == DistinctStrings(strings);
}
// </vc-code>


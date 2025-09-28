predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
lemma SetEquivalenceOnFullSlice(s: seq<int>)
    ensures (set x | x in s[..|s|] && x != 0) == (set x | x in s && x != 0)
{
    ghost var slice_set := set x | x in s[..|s|] && x != 0;
    ghost var full_set := set x | x in s && x != 0;

    forall y | y in slice_set
        ensures y in full_set
    {
        var k :| 0 <= k < |s[..|s|]| && s[..|s|][k] == y;
        assert s[k] == y;
    }

    forall y | y in full_set
        ensures y in slice_set
    {
        var k :| 0 <= k < |s| && s[k] == y;
        assert s[..|s|][k] == y;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result >= 0
    ensures result <= |arr|
    ensures result == DistinctNonZeroCount(arr)
// </vc-spec>
// <vc-code>
{
    var seen: set<int> := {};
    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant seen == (set x | x in arr[..i] && x != 0)
        invariant |seen| <= i
    {
        if arr[i] != 0 {
            seen := seen + {arr[i]};
        }
        i := i + 1;
    }
    result := |seen|;
    SetEquivalenceOnFullSlice(arr);
}
// </vc-code>


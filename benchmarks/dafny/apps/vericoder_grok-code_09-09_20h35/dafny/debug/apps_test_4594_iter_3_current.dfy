predicate ValidInput(diameters: seq<int>)
{
    |diameters| > 0 && forall i :: 0 <= i < |diameters| ==> diameters[i] > 0
}

function num_distinct(s: seq<int>): int
    ensures num_distinct(s) >= 0
    ensures num_distinct(s) <= |s|
    ensures |s| == 0 ==> num_distinct(s) == 0
    ensures |s| > 0 ==> num_distinct(s) >= 1
{
    if |s| == 0 then 0
    else if s[0] in s[1..] then num_distinct(s[1..])
    else 1 + num_distinct(s[1..])
}

// <vc-helpers>
lemma NumDistinctEqualsSetCardinality(s: seq<int>)
    ensures num_distinct(s) == |(set x | x in s)|
{
    if |s| == 0 {
    } else {
        NumDistinctEqualsSetCardinality(s[1..]);
        assert ! (s[0] in s[1..]) || num_distinct(s) == num_distinct(s[1..]);
        assert s[0] in s[1..] ==> |(set x | x in s)| == |(set x | x in s[1..])|;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(diameters: seq<int>) returns (result: int)
    requires ValidInput(diameters)
    ensures result == num_distinct(diameters)
    ensures result >= 1
    ensures result <= |diameters|
// </vc-spec>
// <vc-code>
{
    var distinct: set<int> := {};
    for i := 0 to |diameters| - 1
        invariant distinct == (set x | x in diameters[..i])
    {
        distinct := distinct + {diameters[i]};
    }
    NumDistinctEqualsSetCardinality(diameters);
    result := |distinct|;
}
// </vc-code>


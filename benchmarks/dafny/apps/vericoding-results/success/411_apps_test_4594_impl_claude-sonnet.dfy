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
lemma num_distinct_preserves_membership(s: seq<int>, x: int)
    requires |s| > 0
    ensures x in s <==> (x == s[0] || x in s[1..])
{
}

lemma num_distinct_monotonic(s: seq<int>)
    requires |s| > 0
    ensures num_distinct(s[1..]) <= num_distinct(s)
{
}

lemma num_distinct_correctness(s: seq<int>, seen: set<int>)
    requires forall x :: x in seen <==> x in s
    ensures num_distinct(s) == |seen|
    decreases |s|
{
    if |s| == 0 {
        assert seen == {};
    } else {
        var tail_seen := set x | x in s[1..];
        if s[0] in s[1..] {
            assert seen == tail_seen;
            num_distinct_correctness(s[1..], tail_seen);
        } else {
            assert seen == {s[0]} + tail_seen;
            assert s[0] !in tail_seen;
            num_distinct_correctness(s[1..], tail_seen);
        }
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
    var seen: set<int> := {};
    var i := 0;
    
    while i < |diameters|
        invariant 0 <= i <= |diameters|
        invariant seen == set x | x in diameters[..i]
    {
        seen := seen + {diameters[i]};
        i := i + 1;
    }
    
    result := |seen|;
    
    var full_seen := set x | x in diameters;
    assert seen == full_seen;
    num_distinct_correctness(diameters, full_seen);
}
// </vc-code>


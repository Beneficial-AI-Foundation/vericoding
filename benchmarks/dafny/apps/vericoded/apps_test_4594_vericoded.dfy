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
lemma num_distinct_subset(s: seq<int>, seen: set<int>)
    requires forall x :: x in seen ==> x in s
    ensures num_distinct(s) >= |seen|
{
    if |s| == 0 {
        assert seen == {};
    } else {
        var seen_in_tail := set x | x in seen && x in s[1..];
        if s[0] in seen {
            assert s[0] in s[1..] || seen_in_tail == seen - {s[0]};
            num_distinct_subset(s[1..], seen_in_tail);
        } else {
            num_distinct_subset(s[1..], seen_in_tail);
        }
    }
}

lemma num_distinct_exact(s: seq<int>, seen: set<int>)
    requires forall x :: x in seen <==> exists i :: 0 <= i < |s| && s[i] == x
    ensures num_distinct(s) == |seen|
{
    if |s| == 0 {
        assert seen == {};
    } else {
        var seen_in_tail := set x | x in seen && x in s[1..];
        assert forall x :: x in seen_in_tail <==> x in seen && exists i :: 1 <= i < |s| && s[i] == x;
        assert forall x :: x in seen_in_tail <==> exists i :: 0 <= i < |s[1..]| && s[1..][i] == x by {
            forall x | x in seen_in_tail
            ensures exists i :: 0 <= i < |s[1..]| && s[1..][i] == x
            {
                assert x in seen;
                assert exists i :: 1 <= i < |s| && s[i] == x;
                var k :| 1 <= k < |s| && s[k] == x;
                assert s[1..][k-1] == x;
            }
            forall x | exists i :: 0 <= i < |s[1..]| && s[1..][i] == x
            ensures x in seen_in_tail
            {
                var k :| 0 <= k < |s[1..]| && s[1..][k] == x;
                assert s[k+1] == x;
                assert x in seen;
            }
        }
        
        if s[0] in s[1..] {
            assert s[0] in seen_in_tail;
            assert seen == seen_in_tail;
            num_distinct_exact(s[1..], seen_in_tail);
        } else {
            assert s[0] !in seen_in_tail;
            assert seen == seen_in_tail + {s[0]};
            assert |seen| == |seen_in_tail| + 1;
            num_distinct_exact(s[1..], seen_in_tail);
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
        invariant forall x :: x in seen ==> exists j :: 0 <= j < i && diameters[j] == x
        invariant forall j :: 0 <= j < i ==> diameters[j] in seen
    {
        seen := seen + {diameters[i]};
        i := i + 1;
    }
    
    assert forall x :: x in seen <==> exists j :: 0 <= j < |diameters| && diameters[j] == x;
    num_distinct_exact(diameters, seen);
    
    result := |seen|;
}
// </vc-code>


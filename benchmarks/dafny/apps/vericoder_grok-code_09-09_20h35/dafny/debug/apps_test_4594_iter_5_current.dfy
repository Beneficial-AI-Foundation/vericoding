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
        assert |s| == 0;
        assert num_distinct(s) == 0;
        assert (set x | x in s) == {};
        assert |{}| == 0;
    } else {
        NumDistinctEqualsSetCardinality(s[1..]);
        var set1 := (set x | x in s[1..]);
        var set_total := set1 + {s[0]};
        var card1 := |set1|;
        var card_total := |set_total|;
        var increase := if s[0] in s[1..] then 0 else 1;
        assert card_total == card1 + increase;
        var num_s1 := num_distinct(s[1..]);
        var num_s := if s[0] in s[1..] then num_s1 else 1 + num_s1;
        assert num_distinct(s) == num_s;
        assert num_s1 == card1;
        assert num_s == card1 + (card_total - card1) == card_total;
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
var distinct: set<int> := {};
    for i := 0 to |diameters|
        decreases |diameters| - i
        invariant distinct == (set x | x in diameters[..i])
    {
        distinct := distinct + {diameters[i]};
    }
    NumDistinctEqualsSetCardinality(diameters);
    assert |distinct| == num_distinct(diameters);
    result := |distinct|;
// </vc-code>


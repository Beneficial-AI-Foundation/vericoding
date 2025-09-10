function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

function min_seq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0] else 
        var rest_min := min_seq(s[1..]);
        if s[0] <= rest_min then s[0] else rest_min
}

// <vc-helpers>
function CountNeg(a: seq<int>, i: int): int
    requires 0 <= i <= |a|
    reads a
{
    |set j | 0 <= j < i && a[j] < 0|
}

lemma CountNeg_Step(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures CountNeg(a, i+1) == CountNeg(a, i) + (if a[i] < 0 then 1 else 0)
{
    var set1 := set j | 0 <= j < i && a[j] < 0;
    var set2 := set j | 0 <= j < i+1 && a[j] < 0;
    if a[i] < 0 {
        assert set2 == set1 + {i};
        calc {
            |set2|;
            |set1 + {i}|;
            |set1| + 1;
        }
    } else {
        assert set2 == set1;
        calc {
            |set2|;
            |set1|;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| >= 2
    ensures var count_neg := |set i | 0 <= i < |a| && a[i] < 0|;
            var sum_abs := sum_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]));
            var min_abs := min_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]));
            result == if count_neg % 2 == 0 then sum_abs else sum_abs - 2 * min_abs
// </vc-spec>
// <vc-code>
{
    var count_neg := 0;
    for i := 0 to |a| - 1
        invariant 0 <= i <= |a|
        invariant count_neg == Count
// </vc-code>


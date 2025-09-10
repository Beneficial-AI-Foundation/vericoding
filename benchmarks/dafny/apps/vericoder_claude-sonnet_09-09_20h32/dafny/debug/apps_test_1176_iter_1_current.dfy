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
lemma sum_seq_abs_equivalence(a: seq<int>, abs_a: seq<int>)
    requires |a| == |abs_a|
    requires forall i :: 0 <= i < |a| ==> abs_a[i] == (if a[i] < 0 then -a[i] else a[i])
    ensures sum_seq(abs_a) == sum_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]))

lemma min_seq_abs_equivalence(a: seq<int>, abs_a: seq<int>)
    requires |a| == |abs_a| > 0
    requires forall i :: 0 <= i < |a| ==> abs_a[i] == (if a[i] < 0 then -a[i] else a[i])
    ensures min_seq(abs_a) == min_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]))

function count_negatives(a: seq<int>): int
{
    if |a| == 0 then 0
    else (if a[0] < 0 then 1 else 0) + count_negatives(a[1..])
}

lemma count_negatives_correct(a: seq<int>)
    ensures count_negatives(a) == |set i | 0 <= i < |a| && a[i] < 0|
{
    if |a| == 0 {
    } else {
        count_negatives_correct(a[1..]);
        var s1 := set i | 0 <= i < |a| && a[i] < 0;
        var s2 := set i | 0 <= i < |a[1..]| && a[1..][i] < 0;
        var s3 := set i | 1 <= i < |a| && a[i] < 0;
        assert s2 == s3;
        if a[0] < 0 {
            assert s1 == {0} + s3;
        } else {
            assert s1 == s3;
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
    var abs_a := seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]);
    var count_neg := count_negatives(a);
    var sum_abs := sum_seq(abs_a);
    var min_abs := min_seq(abs_a);
    
    count_negatives_correct(a);
    
    if count_neg % 2 == 0 {
        result := sum_abs;
    } else {
        result := sum_abs - 2 * min_abs;
    }
}
// </vc-code>


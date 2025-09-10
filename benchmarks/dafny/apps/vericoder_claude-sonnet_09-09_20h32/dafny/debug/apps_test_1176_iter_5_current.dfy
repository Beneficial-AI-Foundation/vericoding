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
{
    if |a| == 0 {
    } else {
        var target_seq := seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]);
        var target_tail := seq(|a[1..]|, i requires 0 <= i < |a[1..]| => if a[1..][i] < 0 then -a[1..][i] else a[1..][i]);
        
        assert target_seq[0] == (if a[0] < 0 then -a[0] else a[0]);
        assert abs_a[0] == (if a[0] < 0 then -a[0] else a[0]);
        assert target_seq[0] == abs_a[0];
        
        assert target_seq[1..] == target_tail;
        
        sum_seq_abs_equivalence(a[1..], abs_a[1..]);
        
        assert sum_seq(abs_a) == abs_a[0] + sum_seq(abs_a[1..]);
        assert sum_seq(target_seq) == target_seq[0] + sum_seq(target_seq[1..]);
    }
}

lemma min_seq_abs_equivalence(a: seq<int>, abs_a: seq<int>)
    requires |a| == |abs_a| > 0
    requires forall i :: 0 <= i < |a| ==> abs_a[i] == (if a[i] < 0 then -a[i] else a[i])
    ensures min_seq(abs_a) == min_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]))
{
    if |a| == 1 {
        var target_seq := seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]);
        assert target_seq[0] == (if a[0] < 0 then -a[0] else a[0]);
        assert abs_a[0] == (if a[0] < 0 then -a[0] else a[0]);
    } else {
        var target_seq := seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]);
        var target_tail := seq(|a[1..]|, i requires 0 <= i < |a[1..]| => if a[1..][i] < 0 then -a[1..][i] else a[1..][i]);
        
        assert target_seq[0] == (if a[0] < 0 then -a[0] else a[0]);
        assert abs_a[0] == (if a[0] < 0 then -a[0] else a[0]);
        assert target_seq[0] == abs_a[0];
        
        assert target_seq[1..] == target_tail;
        
        min_seq_abs_equivalence(a[1..], abs_a[1..]);
    }
}

function count_negatives(a: seq<int>): int
{
    if |a| == 0 then 0
    else (if a[0] < 0 then 1 else 0) + count_negatives(a[1..])
}

lemma count_negatives_correct(a: seq<int>)
    ensures count_negatives(a) == |set i | 0 <= i < |a| && a[i] < 0|
    decreases |a|
{
    if |a| == 0 {
    } else {
        count_negatives_correct(a[1..]);
        var s1 := set i | 0 <= i < |a| && a[i] < 0;
        var s2 := set i | 0 <= i < |a[1..]| && a[1..][i] < 0;
        var s3 := set i | 1 <= i < |a| && a[i] < 0;
        
        assert |s2| == count_negatives(a[1..]);
        
        assert s3 == set j {:trigger j in s3} | j in s3;
        assert s2 == set k {:trigger k in s2} | k in s2;
        
        var shift_up := set i {:trigger i + 1} | 0 <= i < |a[1..]| && (i + 1) in s3 :: i;
        var shift_down := set i {:trigger i - 1} | 1 <= i < |a| && (i - 1) in s2 :: i;
        
        assert s2 == shift_up;
        assert s3 == shift_down;
        assert |s2| == |s3|;
        
        if a[0] < 0 {
            assert s1 == {0} + s3;
            assert |s1| == 1 + |s3|;
        } else {
            assert s1 == s3;
            assert |s1| == |s3|;
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
    sum_seq_abs_equivalence(a, abs_a);
    min_seq_abs_equivalence(a, abs_a);
    
    if count_neg % 2 == 0 {
        result := sum_abs;
    } else {
        result := sum_abs - 2 * min_abs;
    }
}
// </vc-code>


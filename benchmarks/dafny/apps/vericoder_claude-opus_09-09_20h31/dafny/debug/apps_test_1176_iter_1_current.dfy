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
lemma sum_seq_append(s: seq<int>, x: int)
    ensures sum_seq(s + [x]) == sum_seq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        calc {
            sum_seq(s + [x]);
            == (s + [x])[0] + sum_seq((s + [x])[1..]);
            == s[0] + sum_seq(s[1..] + [x]);
            == { sum_seq_append(s[1..], x); }
            s[0] + sum_seq(s[1..]) + x;
            == sum_seq(s) + x;
        }
    }
}

lemma min_seq_property(s: seq<int>, i: int)
    requires |s| > 0
    requires 0 <= i < |s|
    ensures min_seq(s) <= s[i]
{
    if |s| == 1 {
        assert i == 0;
    } else if i == 0 {
        if s[0] <= min_seq(s[1..]) {
            assert min_seq(s) == s[0];
        } else {
            assert min_seq(s) == min_seq(s[1..]);
            min_seq_property(s[1..], 0);
        }
    } else {
        min_seq_property(s[1..], i-1);
        if s[0] <= min_seq(s[1..]) {
            assert min_seq(s) == s[0];
        } else {
            assert min_seq(s) == min_seq(s[1..]);
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
    var sum_abs := 0;
    var min_abs := if a[0] < 0 then -a[0] else a[0];
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant count_neg == |set j | 0 <= j < i && a[j] < 0|
        invariant sum_abs == sum_seq(seq(i, j requires 0 <= j < i => if a[j] < 0 then -a[j] else a[j]))
        invariant i > 0 ==> min_abs == min_seq(seq(i, j requires 0 <= j < i => if a[j] < 0 then -a[j] else a[j]))
    {
        var abs_val := if a[i] < 0 then -a[i] else a[i];
        
        if a[i] < 0 {
            count_neg := count_neg + 1;
        }
        
        sum_abs := sum_abs + abs_val;
        
        if i == 0 {
            min_abs := abs_val;
        } else {
            if abs_val < min_abs {
                min_abs := abs_val;
            }
        }
        
        i := i + 1;
    }
    
    if count_neg % 2 == 0 {
        result := sum_abs;
    } else {
        result := sum_abs - 2 * min_abs;
    }
}
// </vc-code>


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
function abs(x: int): int {
    if x < 0 then -x else x
}

function sum_abs_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else abs(s[0]) + sum_abs_seq(s[1..])
}

function min_abs_seq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then abs(s[0]) else 
        var rest_min := min_abs_seq(s[1..]);
        if abs(s[0]) <= rest_min then abs(s[0]) else rest_min
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
    var abs_a := new int[|a|];
    for i := 0 to |a|-1
        invariant 0 <= i <= |a|
        invariant count_neg == |set k | 0 <= k < i && a[k] < 0|
        invariant forall k :: 0 <= k < i ==> abs_a[k] == abs(a[k])
    {
        if a[i] < 0 {
            count_neg := count_neg + 1;
        }
        abs_a[i] := abs(a[i]);
    }

    var sum_total := 0;
    for x_i := 0 to |a|-1
        invariant 0 <= x_i && x_i <= |a|
        invariant sum_total == sum_seq(abs_a[..x_i])
    {
        sum_total := sum_total + abs_a[x_i];
    }

    var min_val := abs_a[0];
    for i := 1 to |a|-1
        invariant 1 <= i && i <= |a|
        invariant min_val == min_seq(abs_a[..i])
        decreases |a| - i
    {
        if abs_a[i] < min_val {
            min_val := abs_a[i];
        }
    }
    
    var s_abs: seq<int> := seq(|a|, i requires 0 <= i < |a| => abs(a[i]));
    
    assert sum_total == sum_abs_seq(s_abs);
    assert min_val == min_abs_seq(s_abs);

    if count_neg % 2 == 0 {
        result := sum_total;
    } else {
        result := sum_total - 2 * min_val;
    }
}
// </vc-code>


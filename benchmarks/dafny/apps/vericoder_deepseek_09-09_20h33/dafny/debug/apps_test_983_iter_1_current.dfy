function max_prefix(s: seq<int>, i: int): int
    requires 0 <= i < |s|
{
    if i == 0 then s[0]
    else if s[i] > max_prefix(s, i-1) then s[i]
    else max_prefix(s, i-1)
}

function max_seq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[|s|-1] > max_seq(s[..|s|-1]) then s[|s|-1]
    else max_seq(s[..|s|-1])
}

function max_expression(n: int, p: int, q: int, r: int, a: seq<int>): int
    requires n > 0
    requires |a| == n
{
    var s1 := seq(n, i requires 0 <= i < n => a[i] * p);
    var s2 := seq(n, i requires 0 <= i < n => max_prefix(s1, i) + a[i] * q);
    var s3 := seq(n, i requires 0 <= i < n => max_prefix(s2, i) + a[i] * r);
    max_seq(s3)
}

predicate ValidInput(n: int, a: seq<int>)
{
    n > 0 && |a| == n
}

// <vc-helpers>
lemma max_prefix_is_max_upto(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures max_prefix(s, i) == max_seq(s[..i+1])
    decreases i
{
    if i > 0 {
        max_prefix_is_max_upto(s, i-1);
        var prev_max := max_seq(s[..i]);
        if s[i] > prev_max {
            assert max_prefix(s, i) == s[i];
            assert max_seq(s[..i+1]) == s[i];
        } else {
            assert max_prefix(s, i) == prev_max;
            assert max_seq(s[..i+1]) == prev_max;
        }
    }
}

function f(s: seq<int>): int
    requires |s| > 0
{
    s[|s|-1]
}

lemma max_seq_tail(s: seq<int>)
    requires |s| > 0
    ensures max_seq(s) == max(max_seq(s[..|s|-1]), s[|s|-1])
{
}

lemma max_seq_monotonic(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures max_seq(s[..i]) <= max_seq(s[..j])
{
    if i < j {
        max_seq_monotonic(s, i, j-1);
        max_seq_tail(s[..j]);
        assert max_seq(s[..j]) == max(max_seq(s[..j-1]), s[j-1]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, q: int, r: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result == max_expression(n, p, q, r, a)
// </vc-spec>
// <vc-code>
{
    var s1 := seq(n, i requires 0 <= i < n => a[i] * p);
    var s2 := seq(n, i requires 0 <= i < n => max_prefix(s1, i) + a[i] * q);
    var s3 := seq(n, i requires 0 <= i < n => max_prefix(s2, i) + a[i] * r);
    
    result := 0;
    var max1 := a[0] * p;
    var max2 := max1 + a[0] * q;
    var max3 := max2 + a[0] * r;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant max1 == max_prefix(s1, i-1) if i > 0 else a[0] * p
        invariant max2 == max_prefix(s2, i-1) if i > 0 else (a[0] * p + a[0] * q)
        invariant max3 == max_prefix(s3, i-1) if i > 0 else (a[0] * p + a[0] * q + a[0] * r)
        invariant result == max_seq(s3[..i]) if i > 0 else (a[0] * p + a[0] * q + a[0] * r)
        decreases n - i
    {
        if i > 0 {
            // Update max1
            if a[i] * p > max1 {
                max1 := a[i] * p;
            }
            // max1 is still max_prefix(s1, i)
            
            // Update max2
            var candidate2 := max1 + a[i] * q;
            if candidate2 > max2 {
                max2 := candidate2;
            }
            // max2 is still max_prefix(s2, i)
            
            // Update max3
            var candidate3 := max2 + a[i] * r;
            if candidate3 > max3 {
                max3 := candidate3;
            }
            // max3 is still max_prefix(s3, i)
            
            // Update result
            if max3 > result {
                result := max3;
            }
        } else {
            result := max3;
        }
        i := i + 1;
    }
}
// </vc-code>


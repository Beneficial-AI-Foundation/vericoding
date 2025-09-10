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

function max(a: int, b: int): int
{
    if a > b then a else b
}

lemma max_seq_tail(s: seq<int>)
    requires |s| > 0
    ensures max_seq(s) == max(max_seq(s[..|s|-1]), s[|s|-1])
{
    if |s| == 1 {
        assert s[..0] == [];
        assert max_seq(s) == s[0];
        assert max(s[0], s[0]) == s[0];
    } else {
        max_seq_tail(s[..|s|-1]);
        assert max_seq(s) == if s[|s|-1] > max_seq(s[..|s|-1]) then s[|s|-1] else max_seq(s[..|s|-1]);
        assert max(max_seq(s[..|s|-1]), s[|s|-1]) == if s[|s|-1] > max_seq(s[..|s|-1]) then s[|s|-1] else max_seq(s[..|s|-1]);
    }
}

lemma max_seq_monotonic(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures max_seq(s[..i]) <= max_seq(s[..j])
{
    if i < j {
        max_seq_monotonic(s, i, j-1);
        max_seq_tail(s[..j]);
        assert max_seq(s[..j]) == max(max_seq(s[..j-1]), s[j-1]);
        assert max_seq(s[..j-1]) <= max_seq(s[..j]);
        assert max_seq(s[..i]) <= max_seq(s[..j-1]);
        assert max_seq(s[..i]) <= max_seq(s[..j]);
    }
}

lemma max_prefix_lemma(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures max_prefix(s, i) == (if i == 0 then s[0] else max(max_prefix(s, i-1), s[i]))
{
    if i > 0 {
        max_prefix_lemma(s, i-1);
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
    var max1 := 0;
    var max2 := 0;
    var max3 := 0;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant i > 0 ==> max1 == max_prefix(s1, i-1)
        invariant i > 0 ==> max2 == max_prefix(s2, i-1)
        invariant i > 0 ==> max3 == max_prefix(s3, i-1)
        invariant i > 0 ==> result == max_seq(s3[..i])
        invariant i == 0 ==> result == 0
        decreases n - i
    {
        if i > 0 {
            // Update max1 for current index i
            var candidate1 := a[i] * p;
            if candidate1 > max1 {
                max1 := candidate1;
            }
            // else max1 remains the same
            
            // Update max2 for current index i
            var candidate2 := max1 + a[i] * q;
            if candidate2 > max2 {
                max2 := candidate2;
            }
            // else max2 remains the same
            
            // Update max3 for current index i
            var candidate3 := max2 + a[i] * r;
            if candidate3 > max3 {
                max3 := candidate3;
            }
            // else max3 remains the same
            
            // Update result
            if max3 > result {
                result := max3;
            }
        } else {
            // Initialize for i = 0
            max1 := a[0] * p;
            max2 := max1 + a[0] * q;
            max3 := max2 + a[0] * r;
            result := max3;
        }
        i := i + 1;
        
        if i > 0 {
            max_prefix_lemma(s1, i-1);
            max_prefix_lemma(s2, i-1);
            max_prefix_lemma(s3, i-1);
            max_seq_tail(s3[..i]);
        }
    }
}
// </vc-code>


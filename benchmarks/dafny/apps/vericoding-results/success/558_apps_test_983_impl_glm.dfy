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
function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var m := max(s[0..|s|-1]);
        if s[|s|-1] > m then s[|s|-1] else m
}

lemma lemma_max_prefix_is_max(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures max_prefix(s, i) == max(s[0..i+1])
{
    if i == 0 {
        assert s[0..1] == [s[0]];
        assert max(s[0..1]) == s[0];
    } else {
        lemma_max_prefix_is_max(s, i-1);
        calc {
            max_prefix(s, i);
            {reveal max_prefix(s, i);}
            if s[i] > max_prefix(s, i-1) then s[i] else max_prefix(s, i-1);
            { lemma_max_prefix_is_max(s, i-1); }
            if s[i] > max(s[0..i]) then s[i] else max(s[0..i]);
            {assert s[0..i+1] == s[0..i] + [s[i]];}
            max(s[0..i] + [s[i]]);
        }
    }
}

lemma lemma_max_seq_is_max(s: seq<int>)
    requires |s| > 0
    ensures max_seq(s) == max(s)
{
    if |s| == 1 {
        assert s == [s[0]];
        assert max_seq(s) == s[0] && max(s) == s[0];
    } else {
        var t := s[..|s|-1];
        lemma_max_seq_is_max(t);
        calc {
            max_seq(s);
            { reveal max_seq(s); }
            if s[|s|-1] > max_seq(t) then s[|s|-1] else max_seq(t);
            == { lemma_max_seq_is_max(t); }
            if s[|s|-1] > max(t) then s[|s|-1] else max(t);
            == { reveal max(s); }
            max(s);
        }
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
    return max_expression(n, p, q, r, a);
}
// </vc-code>


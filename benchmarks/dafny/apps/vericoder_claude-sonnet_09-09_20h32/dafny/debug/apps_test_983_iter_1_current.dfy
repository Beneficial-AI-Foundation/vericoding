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
lemma max_prefix_bounds(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures max_prefix(s, i) in s[..i+1]
{
    if i == 0 {
        assert max_prefix(s, i) == s[0];
        assert s[0] in s[..i+1];
    } else {
        max_prefix_bounds(s, i-1);
        if s[i] > max_prefix(s, i-1) {
            assert max_prefix(s, i) == s[i];
            assert s[i] in s[..i+1];
        } else {
            assert max_prefix(s, i) == max_prefix(s, i-1);
            assert max_prefix(s, i-1) in s[..i];
            assert s[..i] <= s[..i+1];
        }
    }
}

lemma max_prefix_property(s: seq<int>, i: int, j: int)
    requires 0 <= j <= i < |s|
    ensures s[j] <= max_prefix(s, i)
{
    if i == 0 {
        assert j == 0;
        assert max_prefix(s, i) == s[0] == s[j];
    } else {
        if j == i {
            if s[i] > max_prefix(s, i-1) {
                assert max_prefix(s, i) == s[i] == s[j];
            } else {
                assert max_prefix(s, i) == max_prefix(s, i-1);
                max_prefix_property(s, i-1, i-1);
                assert s[i-1] <= max_prefix(s, i-1);
                assert s[i] <= max_prefix(s, i-1);
                assert s[j] == s[i] <= max_prefix(s, i);
            }
        } else {
            max_prefix_property(s, i-1, j);
            if s[i] > max_prefix(s, i-1) {
                assert max_prefix(s, i) == s[i];
                assert s[j] <= max_prefix(s, i-1) < s[i] == max_prefix(s, i);
            } else {
                assert max_prefix(s, i) == max_prefix(s, i-1);
                assert s[j] <= max_prefix(s, i-1) == max_prefix(s, i);
            }
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
    var s1 := seq(n, i requires 0 <= i < n => a[i] * p);
    
    var s2 := new int[n];
    s2[0] := s1[0] + a[0] * q;
    var max_s1 := s1[0];
    
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant max_s1 == max_prefix(s1, i-1)
        invariant forall j :: 0 <= j < i ==> s2[j] == max_prefix(s1, j) + a[j] * q
    {
        if s1[i] > max_s1 {
            max_s1 := s1[i];
        }
        s2[i] := max_s1 + a[i] * q;
        i := i + 1;
    }
    
    var s2_seq := s2[..];
    
    var s3 := new int[n];
    s3[0] := s2_seq[0] + a[0] * r;
    var max_s2 := s2_seq[0];
    
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant max_s2 == max_prefix(s2_seq, i-1)
        invariant forall j :: 0 <= j < i ==> s3[j] == max_prefix(s2_seq, j) + a[j] * r
    {
        if s2_seq[i] > max_s2 {
            max_s2 := s2_seq[i];
        }
        s3[i] := max_s2 + a[i] * r;
        i := i + 1;
    }
    
    var s3_seq := s3[..];
    
    result := s3_seq[0];
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant result == max_seq(s3_seq[..i])
    {
        if s3_seq[i] > result {
            result := s3_seq[i];
        }
        i := i + 1;
    }
}
// </vc-code>


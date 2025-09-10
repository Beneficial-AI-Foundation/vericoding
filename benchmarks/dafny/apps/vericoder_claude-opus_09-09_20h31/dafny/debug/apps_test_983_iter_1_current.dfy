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
lemma max_prefix_lemma(s: seq<int>, i: int, max_so_far: int)
    requires 0 <= i < |s|
    requires i == 0 ==> max_so_far == s[0]
    requires i > 0 ==> max_so_far == max_prefix(s, i-1)
    ensures max(max_so_far, s[i]) == max_prefix(s, i)
{
    if i == 0 {
        assert max_prefix(s, i) == s[0];
        assert max(max_so_far, s[i]) == max(s[0], s[0]) == s[0];
    } else {
        assert max_prefix(s, i) == if s[i] > max_prefix(s, i-1) then s[i] else max_prefix(s, i-1);
        assert max_so_far == max_prefix(s, i-1);
        assert max(max_so_far, s[i]) == if s[i] > max_so_far then s[i] else max_so_far;
    }
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

lemma max_seq_lemma(s: seq<int>, i: int, max_val: int)
    requires |s| > 0
    requires 0 <= i < |s|
    requires i == 0 ==> max_val == s[0]
    requires i > 0 ==> max_val == max_seq(s[..i])
    ensures max(max_val, s[i]) == max_seq(s[..i+1])
{
    if i == 0 {
        assert s[..i+1] == [s[0]];
        assert max_seq(s[..i+1]) == s[0];
    } else {
        assert s[..i+1][..i] == s[..i];
        var prev_seq := s[..i];
        var curr_seq := s[..i+1];
        assert |curr_seq| == i + 1;
        assert curr_seq[|curr_seq|-1] == s[i];
        assert curr_seq[..|curr_seq|-1] == prev_seq;
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
    var s1 := new int[n];
    var s2 := new int[n];
    var s3 := new int[n];
    
    // Compute s1 and track max_prefix for s1
    var max1 := a[0] * p;
    s1[0] := a[0] * p;
    
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> s1[j] == a[j] * p
        invariant max1 == max_prefix(s1[..i], i-1)
    {
        s1[i] := a[i] * p;
        max_prefix_lemma(s1[..i+1], i, max1);
        max1 := max(max1, s1[i]);
        i := i + 1;
    }
    
    // Compute s2 and track max_prefix for s2
    var max2 := s1[0] + a[0] * q;
    s2[0] := s1[0] + a[0] * q;
    
    i := 1;
    max1 := s1[0];
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> s2[j] == max_prefix(s1[..], j) + a[j] * q
        invariant max1 == max_prefix(s1[..], i-1)
        invariant max2 == max_prefix(s2[..i], i-1)
    {
        max_prefix_lemma(s1[..], i, max1);
        max1 := max(max1, s1[i]);
        s2[i] := max1 + a[i] * q;
        max_prefix_lemma(s2[..i+1], i, max2);
        max2 := max(max2, s2[i]);
        i := i + 1;
    }
    
    // Compute s3 and track overall maximum
    var max3 := s2[0] + a[0] * r;
    s3[0] := s2[0] + a[0] * r;
    result := s3[0];
    
    i := 1;
    max2 := s2[0];
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> s3[j] == max_prefix(s2[..], j) + a[j] * r
        invariant max2 == max_prefix(s2[..], i-1)
        invariant result == max_seq(s3[..i])
    {
        max_prefix_lemma(s2[..], i, max2);
        max2 := max(max2, s2[i]);
        s3[i] := max2 + a[i] * r;
        max_seq_lemma(s3[..], i, result);
        result := max(result, s3[i]);
        i := i + 1;
    }
    
    // Prove that the sequences match the functional definitions
    assert s1[..] == seq(n, j requires 0 <= j < n => a[j] * p);
    assert s2[..] == seq(n, j requires 0 <= j < n => max_prefix(s1[..], j) + a[j] * q);
    assert s3[..] == seq(n, j requires 0 <= j < n => max_prefix(s2[..], j) + a[j] * r);
    assert result == max_seq(s3[..]);
}
// </vc-code>


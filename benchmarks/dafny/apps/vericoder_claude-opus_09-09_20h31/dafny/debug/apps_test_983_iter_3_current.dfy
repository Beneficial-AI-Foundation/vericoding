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
    } else {
        assert max_prefix(s, i) == if s[i] > max_prefix(s, i-1) then s[i] else max_prefix(s, i-1);
    }
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

lemma max_seq_update(s: seq<int>, i: int, current_max: int)
    requires 0 < i <= |s|
    requires current_max == max_seq(s[..i])
    ensures max_seq(s[..i+1]) == max(current_max, s[i]) if i < |s| else current_max
{
    if i < |s| {
        var extended := s[..i+1];
        assert extended[..i] == s[..i];
        assert extended[i] == s[i];
        assert |extended| == i + 1;
        
        if i == 1 {
            assert max_seq(extended) == max(s[0], s[1]);
        }
    }
}

lemma seq_construction_lemma(n: int, a: seq<int>, p: int, s1: seq<int>)
    requires n > 0 && |a| == n && |s1| == n
    requires forall j :: 0 <= j < n ==> s1[j] == a[j] * p
    ensures s1 == seq(n, j requires 0 <= j < n => a[j] * p)
{
    assert forall j :: 0 <= j < n ==> s1[j] == (seq(n, k requires 0 <= k < n => a[k] * p))[j];
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, q: int, r: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result == max_expression(n, p, q, r, a)
// </vc-spec>
// <vc-code>
{
    // Arrays to store intermediate values
    var s1 := new int[n];
    var s2 := new int[n];
    var s3 := new int[n];
    
    // Build s1 - simple multiplication
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> s1[j] == a[j] * p
    {
        s1[i] := a[i] * p;
        i := i + 1;
    }
    
    // Build s2 using max prefix of s1
    var max1 := s1[0];
    s2[0] := max1 + a[0] * q;
    
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant max1 == max_prefix(s1[..], i-1)
        invariant forall j :: 0 <= j < i ==> s2[j] == max_prefix(s1[..], j) + a[j] * q
    {
        if s1[i] > max1 {
            max1 := s1[i];
        }
        s2[i] := max1 + a[i] * q;
        i := i + 1;
    }
    
    // Build s3 using max prefix of s2 and compute result
    var max2 := s2[0];
    s3[0] := max2 + a[0] * r;
    result := s3[0];
    
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant max2 == max_prefix(s2[..], i-1)
        invariant forall j :: 0 <= j < i ==> s3[j] == max_prefix(s2[..], j) + a[j] * r
        invariant result == max_seq(s3[..i])
    {
        if s2[i] > max2 {
            max2 := s2[i];
        }
        s3[i] := max2 + a[i] * r;
        
        if s3[i] > result {
            result := s3[i];
        }
        i := i + 1;
    }
    
    // Establish final postcondition
    seq_construction_lemma(n, a, p, s1[..]);
    assert s1[..] == seq(n, j requires 0 <= j < n => a[j] * p);
    assert s2[..] == seq(n, j requires 0 <= j < n => max_prefix(s1[..], j) + a[j] * q);
    assert s3[..] == seq(n, j requires 0 <= j < n => max_prefix(s2[..], j) + a[j] * r);
    assert result == max_seq(s3[..]);
}
// </vc-code>


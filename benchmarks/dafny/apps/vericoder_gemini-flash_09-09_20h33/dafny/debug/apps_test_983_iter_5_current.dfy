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
function max_seq_iter(s: seq<int>, i: int): int
    requires 0 <= i < |s|
    ensures max_seq_iter(s, i) == max_prefix(s, i)
{
    if i == 0 then s[0]
    else if s[i] > max_seq_iter(s, i-1) then s[i]
    else max_seq_iter(s, i-1)
}

lemma max_prefix_is_max_seq_iter(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures max_prefix(s, i) == max_seq_iter(s, i)
{
    if i == 0 {
    } else {
        max_prefix_is_max_seq_iter(s, i-1);
    }
}

lemma max_seq_is_max_prefix_end(s: seq<int>)
    requires |s| > 0
    ensures max_seq(s) == max_prefix(s, |s|-1)
{
    if |s| == 1 {
    } else {
        max_seq_is_max_prefix_end(s[..|s|-1]);
        max_prefix_is_max_seq_iter(s, (|s|-1));
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
    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> s1[j] == a[j] * p
    {
        s1[i] := a[i] * p;
    }

    var s2 := new int[n];
    var current_max_prefix_s1 := 0;
    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> s2[j] == max_prefix(s1[..], j) + a[j] * q
        invariant i == 0 ==> current_max_prefix_s1 == s1[0]
        invariant i > 0 ==> current_max_prefix_s1 == max_prefix(s1[..], i-1)
    {
        if i == 0 {
            current_max_prefix_s1 := s1[0];
            s2[i] := current_max_prefix_s1 + a[i] * q;
        } else {
            max_prefix_is_max_seq_iter(s1[..], i-1);
            if s1[i] > current_max_prefix_s1 {
                current_max_prefix_s1 := s1[i];
            }
            assert current_max_prefix_s1 == max_prefix(s1[..], i);
            s2[i] := current_max_prefix_s1 + a[i] * q;
        }
    }

    var s3 := new int[n];
    var current_max_prefix_s2 := 0;
    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> s3[j] == max_prefix(s2[..], j) + a[j] * r
        invariant i == 0 ==> current_max_prefix_s2 == s2[0]
        invariant i > 0 ==> current_max_prefix_s2 == max_prefix(s2[..], i-1)
    {
        if i == 0 {
            current_max_prefix_s2 := s2[0];
            s3[i] := current_max_prefix_s2 + a[i] * r;
        } else {
            max_prefix_is_max_seq_iter(s2[..], i-1);
            if s2[i] > current_max_prefix_s2 {
                current_max_prefix_s2 := s2[i];
            }
            assert current_max_prefix_s2 == max_prefix(s2[..], i);
            s3[i] := current_max_prefix_s2 + a[i] * r;
        }
    }

    var max_val := s3[0];
    for i := 1 to n-1
        invariant 0 < i <= n
        invariant max_val == max_prefix(s3[..], i-1)
    {
        if s3[i] > max_val {
            max_val := s3[i];
        }
    }
    max_seq_is_max_prefix_end(s3[..]);
    result := max_val;
}
// </vc-code>


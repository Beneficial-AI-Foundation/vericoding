predicate ValidInput(n: int, a: int, b: int, c: int, t: int, arrivals: seq<int>) 
{
    1 <= n <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    1 <= c <= 1000 &&
    1 <= t <= 1000 &&
    |arrivals| == n &&
    forall i :: 0 <= i < |arrivals| ==> 1 <= arrivals[i] <= t
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

function MaxMoney(n: int, a: int, b: int, c: int, t: int, arrivals: seq<int>): int
    requires ValidInput(n, a, b, c, t, arrivals)
{
    if b > c then n * a
    else n * a + (c - b) * (n * t - sum_seq(arrivals))
}

// <vc-helpers>
lemma sum_seq_append(s: seq<int>, x: int)
    ensures sum_seq(s + [x]) == sum_seq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum_seq([x]) == x + sum_seq([]);
        assert sum_seq([]) == 0;
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        sum_seq_append(s[1..], x);
    }
}

lemma sum_seq_prefix(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures sum_seq(s[..i]) + sum_seq(s[i..]) == sum_seq(s)
{
    if i == 0 {
        assert s[..0] == [];
        assert s[0..] == s;
    } else if i == |s| {
        assert s[..|s|] == s;
        assert s[|s|..] == [];
    } else {
        assert s == s[..i] + s[i..];
        var prefix := s[..i];
        var suffix := s[i..];
        if |prefix| == 0 {
            assert sum_seq(prefix) == 0;
        } else {
            assert s[0] == prefix[0];
            assert s[1..] == prefix[1..] + suffix;
            sum_seq_prefix(s[1..], i-1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, c: int, t: int, arrivals: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, c, t, arrivals)
    ensures result == MaxMoney(n, a, b, c, t, arrivals)
// </vc-spec>
// <vc-code>
{
    if b > c {
        result := n * a;
    } else {
        var total_sum := 0;
        var i := 0;
        
        while i < |arrivals|
            invariant 0 <= i <= |arrivals|
            invariant total_sum == sum_seq(arrivals[..i])
        {
            sum_seq_prefix(arrivals, i);
            assert arrivals[..i+1] == arrivals[..i] + [arrivals[i]];
            sum_seq_append(arrivals[..i], arrivals[i]);
            total_sum := total_sum + arrivals[i];
            i := i + 1;
        }
        
        assert arrivals[..|arrivals|] == arrivals;
        assert total_sum == sum_seq(arrivals);
        
        result := n * a + (c - b) * (n * t - total_sum);
    }
}
// </vc-code>


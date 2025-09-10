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
lemma sum_seq_distributive(s: seq<int>, k: int)
    ensures sum_seq(s) * k == k * sum_seq(s)
{
}

lemma sum_seq_computation(arrivals: seq<int>)
    requires |arrivals| > 0
    ensures sum_seq(arrivals) == arrivals[0] + sum_seq(arrivals[1..])
{
}

lemma sum_seq_bounds(arrivals: seq<int>, t: int)
    requires forall i :: 0 <= i < |arrivals| ==> 1 <= arrivals[i] <= t
    ensures sum_seq(arrivals) >= |arrivals|
    ensures sum_seq(arrivals) <= |arrivals| * t
{
    if |arrivals| == 0 {
    } else {
        sum_seq_bounds(arrivals[1..], t);
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
        var total_wait_time := n * t - sum_seq(arrivals);
        result := n * a + (c - b) * total_wait_time;
    }
}
// </vc-code>


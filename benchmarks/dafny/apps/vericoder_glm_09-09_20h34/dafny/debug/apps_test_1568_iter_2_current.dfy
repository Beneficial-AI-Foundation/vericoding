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
lemma sum_append(s: seq<int>, x: int)
    ensures sum_seq(s + [x]) == sum_seq(s) + x
    decreases |s|
{
    if |s| == 0 {
    } else {
        calc {
            sum_seq(s + [x]);
            == { definition of sum_seq }
            s[0] + sum_seq(s[1..] + [x]);
            == { sum_append(s[1..], x) }
            s[0] + (sum_seq(s[1..]) + x);
            == { associativity }
            (s[0] + sum_seq(s[1..])) + x;
            == { definition of sum_seq }
            sum_seq(s) + x;
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
    var totalArrival := 0;
    for i := 0 to n
        invariant 0 <= i <= n
        invariant totalArrival == sum_seq(arrivals[0..i])
    {
        totalArrival := totalArrival + arrivals[i];
    }
    if b > c {
        result := n * a;
    } else {
        result := n * a + (c - b) * (n * t - totalArrival);
    }
}
// </vc-code>


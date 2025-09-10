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
lemma SumLemma(arrivals: seq<int>, t: int, n: int)
  requires n == |arrivals|
  requires forall i :: 0 <= i < |arrivals| ==> 1 <= arrivals[i] <= t
  ensures n * t - sum_seq(arrivals) == sum_seq(SeqDiff(arrivals, t))
{
  SumDiffLemma(arrivals, t);
}

ghost function SeqDiff(s: seq<int>, t: int): seq<int>
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= t
{
  if |s| == 0 then []
  else [t - s[0]] + SeqDiff(s[1..], t)
}

lemma SumDiffLemma(s: seq<int>, t: int)
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= t
  ensures sum_seq(SeqDiff(s, t)) == |s| * t - sum_seq(s)
{
  if |s| > 0 {
    calc == {
      sum_seq(SeqDiff(s, t));
      (t - s[0]) + sum_seq(SeqDiff(s[1..], t));
      (t - s[0]) + (|s[1..]| * t - sum_seq(s[1..]));
      t - s[0] + ((|s| - 1) * t - sum_seq(s[1..]));
      t - s[0] + (|s| * t - t - sum_seq(s[1..]));
      |s| * t - s[0] - sum_seq(s[1..]);
      |s| * t - (s[0] + sum_seq(s[1..]));
      |s| * t - sum_seq(s);
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
    var diff_sum := 0;
    var i := 0;
    while i < n 
      invariant 0 <= i <= n
      invariant diff_sum == sum_seq(SeqDiff(arrivals[0..i], t))
    {
      diff_sum := diff_sum + (t - arrivals[i]);
      i := i + 1;
    }
    SumDiffLemma(arrivals, t);
    result := n * a + (c - b) * diff_sum;
  }
}
// </vc-code>


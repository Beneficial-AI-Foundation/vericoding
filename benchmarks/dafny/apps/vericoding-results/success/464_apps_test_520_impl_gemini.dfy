function sumRange(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start == end then 0
    else s[start] + sumRange(s, start + 1, end)
}

predicate ValidInput(n: int, years: seq<int>)
{
    n > 0 && |years| == n
}

// <vc-helpers>
lemma sumRange_split(s: seq<int>, a: int, b: int, c: int)
    requires 0 <= a <= b <= c <= |s|
    ensures sumRange(s, a, c) == sumRange(s, a, b) + sumRange(s, b, c)
    decreases b - a
{
    if a < b {
        sumRange_split(s, a + 1, b, c);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, years: seq<int>) returns (result: int)
    requires ValidInput(n, years)
    ensures result == sumRange(years, 0, |years|) / n
// </vc-spec>
// <vc-code>
{
  var sum: int := 0;
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |years| == n
    invariant sum == sumRange(years, 0, i)
    decreases n - i
  {
    sumRange_split(years, 0, i, i + 1);
    sum := sum + years[i];
    i := i + 1;
  }
  result := sum / n;
}
// </vc-code>


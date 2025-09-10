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
lemma sumRange_add_one(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures sumRange(s, 0, |s|) == sumRange(s, 0, k) + s[k] + sumRange(s, k+1, |s|)
{
  if k > 0 {
    sumRange_add_one(s[1..], k-1);
  } else {
    // Base case when k == 0
  }
}

lemma sumRange_zero(s: seq<int>)
  ensures sumRange(s, 0, 0) == 0
{
}

lemma sumRange_empty(s: seq<int>, start: int, end: int)
  requires start == end
  ensures sumRange(s, start, end) == 0
{
}

lemma sumRange_recursive(s: seq<int>, start: int, end: int)
  requires 0 <= start < end <= |s|
  ensures sumRange(s, start, end) == s[start] + sumRange(s, start + 1, end)
{
}

lemma sumRange_loop_lemma(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sumRange(s, 0, i) == sumRange(s, 0, i)
{
}

lemma sumRange_split(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures sumRange(s, 0, j) == sumRange(s, 0, i) + sumRange(s, i, j)
  decreases j - i
{
  if i < j {
    sumRange_recursive(s, i, j);
    sumRange_split(s, i, j-1);
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
  var sum := 0;
  var i := 0;
  while i < |years|
    invariant 0 <= i <= |years|
    invariant sum == sumRange(years, 0, i)
  {
    sumRange_split(years, i, i+1);
    sum := sum + years[i];
    i := i + 1;
  }
  result := sum / n;
}
// </vc-code>


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
    var s' := s[1..];
    assert |s'| == |s| - 1;
    assert s == [s[0]] + s';
    sumRange_add_one(s', k-1);
  } else {
    // Base case when k == 0
    assert sumRange(s, 0, 0) == 0;
    assert sumRange(s, 1, |s|) == sumRange(s, 0, |s|) - s[0] by {
      if |s| > 1 {
        sumRange_split(s, 0, 1);
      }
    };
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
    sumRange_split(s, i, j - 1);
    sumRange_recursive(s, j - 1, j);
    assert sumRange(s, 0, j) == sumRange(s, 0, j - 1) + s[j - 1];
    assert sumRange(s, i, j) == sumRange(s, i, j - 1) + s[j - 1];
  } else {
    sumRange_empty(s, i, j);
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
    assert sumRange(years, i, i+1) == years[i] by {
      sumRange_recursive(years, i, i+1);
      sumRange_empty(years, i+1, i+1);
    };
    sum := sum + years[i];
    i := i + 1;
  }
  result := sum / n;
}
// </vc-code>


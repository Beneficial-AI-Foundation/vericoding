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
lemma SumRangeSplit(s: seq<int>, start: int, mid: int, end_: int)
  requires 0 <= start <= mid <= end_ <= |s|
  ensures sumRange(s, start, end_) == sumRange(s, start, mid) + sumRange(s, mid, end_)
  decreases end_ - start
{
  if start == end_ {
    // all zero-length ranges
    assert sumRange(s, start, end_) == 0;
    assert sumRange(s, start, mid) == 0;
    assert sumRange(s, mid, end_) == 0;
  } else if start < mid {
    // unfold definitions
    assert sumRange(s, start, end_) == s[start] + sumRange(s, start + 1, end_);
    assert sumRange(s, start, mid) == s[start] + sumRange(s, start + 1, mid);
    SumRangeSplit(s, start + 1, mid, end_);
    assert s[start] + sumRange(s, start + 1, end_) == s[start] + (sumRange(s, start + 1, mid) + sumRange(s, mid, end_));
    assert s[start] + (sumRange(s, start + 1, mid) + sumRange(s, mid, end_)) == (s[start] + sumRange(s, start + 1, mid)) + sumRange(s, mid, end_);
    assert (s[start] + sumRange(s, start + 1, mid)) + sumRange(s, mid, end_) == sumRange(s, start, mid) + sumRange(s, mid, end_);
  } else {
    // start >= mid, with start <= mid implies start == mid
    assert start == mid;
    assert sumRange(s, start, mid) == 0;
    assert sumRange(s, mid, end_) == sumRange(s, start, end_);
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
  var i := 0;
  var s := 0;
  while i < |years|
    invariant 0 <= i <= |years|
    invariant s == sumRange(years, 0, i)
    decreases |years| - i
  {
    var oldi := i;
    s := s + years[oldi];
    i := oldi + 1;
    // Use splitting lemma to justify the invariant update:
    SumRangeSplit(years, 0, oldi, oldi + 1);
    assert sumRange(years, 0, oldi + 1) == sumRange(years, 0, oldi) + sumRange(years, oldi, oldi + 1);
    assert sumRange(years, oldi, oldi + 1) == years[oldi] + sumRange(years, oldi + 1, oldi + 1);
    assert sumRange(years, oldi + 1, oldi + 1) == 0;
    assert sumRange(years, oldi, oldi + 1) == years[oldi];
    assert s == sumRange(years, 0, i);
  }
  result := s / n;
}
// </vc-code>


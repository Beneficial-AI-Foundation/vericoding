predicate ValidInput(n: int, a: seq<int>, s: int, f: int)
{
  n >= 2 && |a| == n && s >= 1 && f > s && f <= n &&
  forall i :: 0 <= i < n ==> a[i] >= 1
}

function participantCount(a: seq<int>, s: int, f: int, n: int, start: int): int
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
{
  participantCountHelper(a, s, f, n, start, 0)
}

function participantCountHelper(a: seq<int>, s: int, f: int, n: int, start: int, i: int): int
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= n
  decreases n - i
{
  if i >= n then 0
  else
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    contribution + participantCountHelper(a, s, f, n, start, i + 1)
}

// <vc-helpers>
lemma participantCountShift(a: seq<int>, s: int, f: int, n: int, start: int, k: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= k <= n
  ensures participantCountHelper(a, s, f, n, start, k) >= 0
  decreases n - k
{
  if k < n {
    participantCountShift(a, s, f, n, start, k + 1);
    var localHour := (start + k - 1) % n + 1;
    var contribution := if s <= localHour < f then a[k] else 0;
    assert a[k] >= 0;
    assert contribution >= 0;
  }
}

lemma participantCountMonotonic(a: seq<int>, s: int, f: int, n: int, start: int, i: int, j: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= j <= n
  ensures participantCountHelper(a, s, f, n, start, i) >= participantCountHelper(a, s, f, n, start, j)
  decreases j - i
{
  if i < j {
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    assert participantCountHelper(a, s, f, n, start, i) == contribution + participantCountHelper(a, s, f, n, start, i + 1);
    participantCountMonotonic(a, s, f, n, start, i + 1, j);
    assert contribution >= 0 by {
      participantCountShift(a, s, f, n, start, i);
    }
  }
}

lemma participantCountAdditive(a: seq<int>, s: int, f: int, n: int, start: int, i: int, j: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= j <= n
  ensures participantCountHelper(a, s, f, n, start, i) == 
          participantCountHelper(a, s, f, n, start, j) + 
          sumContributions(a, s, f, n, start, i, j)
  decreases j - i
{
  if i < j {
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    assert participantCountHelper(a, s, f, n, start, i) == contribution + participantCountHelper(a, s, f, n, start, i + 1);
    participantCountAdditive(a, s, f, n, start, i + 1, j);
    assert sumContributions(a, s, f, n, start, i, j) == contribution + sumContributions(a, s, f, n, start, i + 1, j);
  }
}

ghost function sumContributions(a: seq<int>, s: int, f: int, n: int, start: int, i: int, j: int): int
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= j <= n
  decreases j - i
{
  if i >= j then 0
  else 
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    contribution + sumContributions(a, s, f, n, start, i + 1, j)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, s: int, f: int) returns (result: int)
  requires ValidInput(n, a, s, f)
  ensures 1 <= result <= n
  ensures forall start :: 1 <= start <= n ==> 
    participantCount(a, s, f, n, result) >= participantCount(a, s, f, n, start)
  ensures forall start :: 1 <= start <= n && 
    participantCount(a, s, f, n, start) == participantCount(a, s, f, n, result) 
    ==> result <= start
// </vc-spec>
// <vc-code>
{
  result := 1;
  var maxCount := participantCount(a, s, f, n, 1);
  var start := 2;
  
  while start <= n
    invariant 1 <= start <= n + 1
    invariant 1 <= result <= n
    invariant maxCount == participantCount(a, s, f, n, result)
    invariant forall s' :: 1 <= s' < start ==> maxCount >= participantCount(a, s, f, n, s')
    invariant forall s' :: 1 <= s' < start && participantCount(a, s, f, n, s') == maxCount ==> result <= s'
  {
    var currentCount := participantCount(a, s, f, n, start);
    assert currentCount >= 0 by {
      participantCountShift(a, s, f, n, start, 0);
    }
    if currentCount > maxCount {
      result := start;
      maxCount := currentCount;
    } else if currentCount == maxCount && start < result {
      result := start;
    }
    start := start + 1;
  }
}
// </vc-code>


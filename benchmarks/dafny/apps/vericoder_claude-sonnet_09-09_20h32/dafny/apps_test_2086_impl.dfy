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
lemma participantCountBounds(a: seq<int>, s: int, f: int, n: int, start: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires forall i :: 0 <= i < n ==> a[i] >= 1
  ensures participantCount(a, s, f, n, start) >= 1
{
  participantCountHelperBounds(a, s, f, n, start, 0);
}

lemma participantCountHelperBounds(a: seq<int>, s: int, f: int, n: int, start: int, i: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= n
  requires forall j :: 0 <= j < n ==> a[j] >= 1
  ensures participantCountHelper(a, s, f, n, start, i) >= 0
  ensures i == 0 ==> participantCountHelper(a, s, f, n, start, i) >= 1
  decreases n - i
{
  if i >= n {
  } else {
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    participantCountHelperBounds(a, s, f, n, start, i + 1);
    
    if i == 0 {
      hoursFormPermutation(n, start);
      assert exists k {:trigger a[k]} :: 0 <= k < n && (start + k - 1) % n + 1 == s;
      var k :| 0 <= k < n && (start + k - 1) % n + 1 == s;
      assert s <= (start + k - 1) % n + 1 < f;
      assert a[k] >= 1;
      assert participantCountHelper(a, s, f, n, start, i) >= a[k] >= 1;
    }
  }
}

lemma hoursFormPermutation(n: int, start: int)
  requires n >= 1
  requires 1 <= start <= n
  ensures (forall h :: 1 <= h <= n ==> 
    (exists j {:trigger a[j]} :: 0 <= j < n && (start + j - 1) % n + 1 == h))
{
  forall h | 1 <= h <= n 
  ensures (exists j {:trigger a[j]} :: 0 <= j < n && (start + j - 1) % n + 1 == h)
  {
    var j := if h >= start then h - start else n - start + h;
    
    if h >= start {
      assert j == h - start;
      assert 0 <= j <= n - 1;
      assert start + j == h;
      assert (start + j - 1) % n + 1 == (h - 1) % n + 1 == h;
    } else {
      assert j == n - start + h;
      assert j == n - (start - h);
      assert 0 <= j < n;
      assert start + j - 1 == start + n - start + h - 1 == n + h - 1;
      assert (start + j - 1) % n + 1 == (n + h - 1) % n + 1 == (h - 1) + 1 == h;
    }
    
    assert 0 <= j < n;
    assert (start + j - 1) % n + 1 == h;
  }
}

lemma participantCountEquiv(a: seq<int>, s: int, f: int, n: int, start: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  ensures participantCount(a, s, f, n, start) == participantCountHelper(a, s, f, n, start, 0)
{
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
  var maxCount := participantCount(a, s, f, n, 1);
  var bestStart := 1;
  var current := 2;
  
  participantCountBounds(a, s, f, n, 1);
  
  while current <= n
    invariant 2 <= current <= n + 1
    invariant 1 <= bestStart <= current - 1
    invariant maxCount == participantCount(a, s, f, n, bestStart)
    invariant (forall start :: 1 <= start < current ==> 
      participantCount(a, s, f, n, bestStart) >= participantCount(a, s, f, n, start))
    invariant (forall start :: 1 <= start < current && 
      participantCount(a, s, f, n, start) == participantCount(a, s, f, n, bestStart) 
      ==> bestStart <= start)
  {
    var currentCount := participantCount(a, s, f, n, current);
    
    if currentCount > maxCount {
      maxCount := currentCount;
      bestStart := current;
    } else if currentCount == maxCount && current < bestStart {
      bestStart := current;
    }
    
    current := current + 1;
  }
  
  result := bestStart;
}
// </vc-code>


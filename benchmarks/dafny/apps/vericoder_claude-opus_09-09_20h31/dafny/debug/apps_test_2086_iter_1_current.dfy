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
lemma ParticipantCountBounded(a: seq<int>, s: int, f: int, n: int, start: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires forall i :: 0 <= i < n ==> a[i] >= 1
  ensures participantCount(a, s, f, n, start) >= 0
{
  var count := participantCountHelper(a, s, f, n, start, 0);
  ParticipantCountHelperNonNegative(a, s, f, n, start, 0);
}

lemma ParticipantCountHelperNonNegative(a: seq<int>, s: int, f: int, n: int, start: int, i: int)
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= n
  requires forall j :: 0 <= j < n ==> a[j] >= 1
  ensures participantCountHelper(a, s, f, n, start, i) >= 0
  decreases n - i
{
  if i >= n {
    // Base case: returns 0
  } else {
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    ParticipantCountHelperNonNegative(a, s, f, n, start, i + 1);
  }
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
  
  var currentStart := 2;
  
  while currentStart <= n
    invariant 1 <= bestStart <= n
    invariant 1 <= currentStart <= n + 1
    invariant forall start :: 1 <= start < currentStart ==> 
      participantCount(a, s, f, n, bestStart) >= participantCount(a, s, f, n, start)
    invariant forall start :: 1 <= start < currentStart && 
      participantCount(a, s, f, n, start) == participantCount(a, s, f, n, bestStart) 
      ==> bestStart <= start
    invariant maxCount == participantCount(a, s, f, n, bestStart)
  {
    var currentCount := participantCount(a, s, f, n, currentStart);
    
    if currentCount > maxCount {
      maxCount := currentCount;
      bestStart := currentStart;
    }
    
    currentStart := currentStart + 1;
  }
  
  return bestStart;
}
// </vc-code>


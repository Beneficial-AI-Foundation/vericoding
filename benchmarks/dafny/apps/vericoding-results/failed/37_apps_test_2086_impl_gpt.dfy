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
module {:options "--allow-warnings"} AllowWarnings {}
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
  var i := 1;
  var bestStart := 1;
  var bestVal := participantCount(a, s, f, n, 1);
  while i <= n
    invariant 1 <= i <= n + 1
    invariant 1 <= bestStart <= n
    invariant bestVal == participantCount(a, s, f, n, bestStart)
    invariant forall t :: 1 <= t < i ==> participantCount(a, s, f, n, bestStart) >= participantCount(a, s, f, n, t)
    invariant forall t :: 1 <= t < i && participantCount(a, s, f, n, t) == participantCount(a, s, f, n, bestStart) ==> bestStart <= t
    decreases n + 1 - i
  {
    var cur := participantCount(a, s, f, n, i);
    if cur > bestVal || (cur == bestVal && i < bestStart) {
      bestVal := cur;
      bestStart := i;
    }
    i := i + 1;
  }
  result := bestStart;
}
// </vc-code>


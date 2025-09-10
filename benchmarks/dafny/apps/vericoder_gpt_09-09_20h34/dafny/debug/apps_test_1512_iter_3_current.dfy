predicate ValidPermutation(p: seq<int>, n: int)
{
  |p| == n && n >= 1 &&
  (forall i :: 0 <= i < n ==> 1 <= p[i] <= n) &&
  (forall i, j :: 0 <= i < j < n ==> p[i] != p[j])
}

function countRecords(s: seq<int>): int
  ensures countRecords(s) >= 0
{
  if |s| == 0 then 0
  else 1 + countRecordsFromIndex(s, 1, s[0])
}

function countRecordsAfterRemoval(p: seq<int>, toRemove: int): int
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  requires toRemove in p
{
  var filtered := seq(|p| - 1, i requires 0 <= i < |p| - 1 => 
    if indexOf(p, toRemove) <= i then p[i + 1] else p[i]);
  countRecords(filtered)
}

// <vc-helpers>
function countRecordsFromIndex(s: seq<int>, i: int, currentMax: int): int
  decreases if i <= |s| then |s| - i else 0
{
  if i >= |s| then 0
  else if s[i] > currentMax then 1 + countRecordsFromIndex(s, i + 1, s[i])
  else countRecordsFromIndex(s, i + 1, currentMax)
}

function indexOf(p: seq<int>, x: int): int
  requires x in p
  ensures 0 <= indexOf(p, x) < |p|
  ensures p[indexOf(p, x)] == x
  decreases |p|
{
  if p[0] == x then 0 else 1 + indexOf(p[1..], x)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
  requires ValidPermutation(p, n)
  ensures 1 <= result <= n
  ensures result in p
  ensures forall x :: x in p ==> countRecordsAfterRemoval(p, result) >= countRecordsAfterRemoval(p, x)
  ensures forall x :: x in p && countRecordsAfterRemoval(p, x) == countRecordsAfterRemoval(p, result) ==> result <= x
// </vc-spec>
// <vc-code>
{
  var best := p[0];
  var bestVal := countRecordsAfterRemoval(p, best);
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant best in p[..i]
    invariant bestVal == countRecordsAfterRemoval(p, best)
    invariant forall x :: x in p[..i] ==> bestVal >= countRecordsAfterRemoval(p, x)
    invariant forall x :: x in p[..i] && countRecordsAfterRemoval(p, x) == bestVal ==> best <= x
    decreases n - i
  {
    var candidate := p[i];
    var val := countRecordsAfterRemoval(p, candidate);
    if val > bestVal || (val == bestVal && candidate < best) {
      best := candidate;
      bestVal := val;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>


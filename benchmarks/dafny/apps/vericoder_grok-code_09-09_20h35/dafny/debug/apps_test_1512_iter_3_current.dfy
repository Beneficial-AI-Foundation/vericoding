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
function countRecordsFromIndex(s: seq<int>, idx: nat, currentMax: int): nat
  requires 0 <= idx <= |s|
  decreases |s| - idx
{
  if idx >= |s| then 0
  else if s[idx] > currentMax then 1 + countRecordsFromIndex(s, idx + 1, s[idx])
  else countRecordsFromIndex(s, idx + 1, currentMax)
}

function countRecordsAfterRemoval(p: seq<int>, toRemove: int): int
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  requires toRemove in p
{
  var idx := p.IndexOf(toRemove);
  var filtered := p[..idx] + p[idx + 1..];
  countRecords(filtered)
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
  result := 1;
  var maxCount := countRecordsAfterRemoval(p, 1);
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant forall k :: 1 <= k < i ==> countRecordsAfterRemoval(p, result) >= countRecordsAfterRemoval(p, k)
    invariant forall k :: 1 <= k < i && countRecordsAfterRemoval(p, k) == countRecordsAfterRemoval(p, result) ==> result <= k
  {
    var currentCount := countRecordsAfterRemoval(p, i);
    if currentCount > maxCount || (currentCount == maxCount && i < result) {
      maxCount := currentCount;
      result := i;
    }
    i := i + 1;
  }
}
// </vc-code>


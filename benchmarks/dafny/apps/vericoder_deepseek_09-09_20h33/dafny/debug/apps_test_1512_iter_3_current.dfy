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
function countRecordsFromIndex(s: seq<int>, idx: int, maxSoFar: int): int
  requires |s| >= 1
  requires 0 <= idx <= |s|
  requires 0 <= maxSoFar
  ensures countRecordsFromIndex(s, idx, maxSoFar) >= 0
  decreases |s| - idx
{
  if idx >= |s| then 0
  else (if s[idx] > maxSoFar then 1 else 0)
       + countRecordsFromIndex(s, idx + 1, if maxSoFar >= s[idx] then maxSoFar else s[idx])
}

function indexOf(s: seq<int>, value: int): int
  requires value in s
  ensures 0 <= indexOf(s, value) < |s|
  ensures s[indexOf(s, value)] == value
  ensures forall i :: 0 <= i < indexOf(s, value) ==> s[i] != value
  decreases |s|
{
  if s[0] == value then 0
  else indexOf(s[1..], value) + 1
}

lemma CountRecordsLemma(s: seq<int>)
  requires |s| >= 1
  ensures countRecords(s) == 1 + countRecordsFromIndex(s, 1, s[0])
{
}

lemma CountRecordsAfterRemovalLemma(p: seq<int>, toRemove: int, q: seq<int>)
  requires |p| >= 1
  requires toRemove in p
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  requires q == seq(|p| - 1, i requires 0 <= i < |p| - 1 => 
    if indexOf(p, toRemove) <= i then p[i + 1] else p[i])
  ensures countRecordsAfterRemoval(p, toRemove) >= 0
{
}

lemma CountRecordsPreservation(p: seq<int>, toRemove: int, x: int)
  requires |p| >= 1
  requires toRemove in p
  requires x in p
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  ensures countRecordsAfterRemoval(p, x) >= 0
{
}

lemma AllElementsHaveValidCounts(p: seq<int>)
  requires ValidPermutation(p, |p|)
  ensures forall x :: x in p ==> countRecordsAfterRemoval(p, x) >= 0
{
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
  var minRecord := p[0];
  var minCount := countRecordsAfterRemoval(p, p[0]);
  var i := 1;
  
  while i < n
    invariant 1 <= i <= n
    invariant minRecord in p
    invariant minCount == countRecordsAfterRemoval(p, minRecord)
    invariant forall j :: 0 <= j < i ==> countRecordsAfterRemoval(p, minRecord) <= countRecordsAfterRemoval(p, p[j])
    invariant forall j :: 0 <= j < i && countRecordsAfterRemoval(p, p[j]) == countRecordsAfterRemoval(p, minRecord) ==> minRecord <= p[j]
  {
    var currentCount := countRecordsAfterRemoval(p, p[i]);
    assert currentCount >= 0;
    if currentCount < minCount {
      minRecord := p[i];
      minCount := currentCount;
    } else if currentCount == minCount && p[i] < minRecord {
      minRecord := p[i];
    }
    i := i + 1;
  }
  
  result := minRecord;
}
// </vc-code>


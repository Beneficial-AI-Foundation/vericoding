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
function method indexOf<T>(s: seq<T>, x: T): int
  requires x in s
  ensures 0 <= indexOf(s, x) < |s|
  ensures s[indexOf(s, x)] == x
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
  {
    if s[i] == x then
      return i;
    i := i + 1;
  }
  return -1; // Should not reach here due to precondition
}
function countRecordsFromIndex(s: seq<int>, index: int, currentMax: int): int
  requires 0 <= index <= |s|
  ensures countRecordsFromIndex(s, index, currentMax) >= 0
{
  if index == |s| then 0
  else
    var nextMax := currentMax;
    if s[index] > currentMax then
      nextMax := s[index];
    var count := countRecordsFromIndex(s, index + 1, nextMax);
    if s[index] > currentMax then
      count := count + 1;
    count
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
  var minCount := n + 1; // max possible countRecords is n
  var bestResult := -1;

  var currentMinCount := n + 1;
  var currentBestResult := -1;

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant (bestResult == -1 && i == 0) || (bestResult in p && 1 <= bestResult <= n)
    invariant forall x :: x in p && (indexOf(p, x) < i) ==> countRecordsAfterRemoval(p, currentBestResult) >= countRecordsAfterRemoval(p, x)
    invariant (currentBestResult == -1 && i == 0) || currentMinCount == countRecordsAfterRemoval(p, currentBestResult)
    invariant (currentBestResult == -1 && i == 0) || forall x :: x in p && (indexOf(p, x) < i) && countRecordsAfterRemoval(p, x) == currentMinCount ==> currentBestResult <= x
  {
    var x := p[i];
    var numRecords := countRecordsAfterRemoval(p, x);

    if numRecords < currentMinCount
    {
      currentMinCount := numRecords;
      currentBestResult := x;
    } else if numRecords == currentMinCount
    {
      if x < currentBestResult
      {
        currentBestResult := x;
      }
    }
  }
  return currentBestResult;
}
// </vc-code>


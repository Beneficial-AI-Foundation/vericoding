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
function indexOf<T>(s: seq<T>, x: T): int
  requires x in s
  ensures 0 <= indexOf(s, x) < |s|
  ensures s[indexOf(s, x)] == x
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] != x
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
    var count := 0;
    if s[index] > currentMax then
      nextMax := s[index];
      count := 1;
    // The previous implementation had an issue with the recursive call when index + 1 > |s|.
    // While the precondition 0 <= index <= |s| and the base case index == |s| cover a lot,
    // the recursive call needs to ensure index + 1 is also a valid index for a smaller problem.
    // However, if index + 1 == |s|, the next call will hit the base case, so no explicit check is needed here
    // other than ensuring the argument for the next recursive call is correct.
    count + countRecordsFromIndex(s, index + 1, nextMax)
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
  var currentMinCount := n + 1;
  var currentBestResult := -1;

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant (currentBestResult == -1 && i == 0) || (currentBestResult in p && 1 <= currentBestResult <= n)
    invariant (currentBestResult == -1 && i == 0) || countRecordsAfterRemoval(p, currentBestResult) == currentMinCount
    invariant (currentBestResult == -1 && i == 0) || (forall x_val :: (exists k :: 0 <= k < i && x_val == p[k]) ==> currentMinCount <= countRecordsAfterRemoval(p, x_val))
    invariant (currentBestResult == -1 && i == 0) || (forall x_val :: (exists k :: 0 <= k < i && x_val == p[k]) && countRecordsAfterRemoval(p, x_val) == currentMinCount ==> currentBestResult <= x_val)
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


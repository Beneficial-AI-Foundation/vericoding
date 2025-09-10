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
function countRecordsFromIndex(s: seq<int>, i: int, maxSoFar: int): int
  requires 0 <= i <= |s|
  requires |s| > 0 ==> 1 <= maxSoFar
  ensures countRecordsFromIndex(s, i, maxSoFar) >= 0
{
  if i == |s| then 0
  else (if maxSoFar < s[i] then 1 else 0) + countRecordsFromIndex(s, i + 1, max(maxSoFar, s[i]))
}

lemma countRecordsFromIndexCorrect(s: seq<int>, i: int, maxSoFar: int)
  requires 0 <= i <= |s|
  requires |s| > 0 ==> 1 <= maxSoFar
  ensures countRecordsFromIndex(s, i, maxSoFar) == 
    (if i < |s| then (if maxSoFar < s[i] then 1 else 0) + countRecordsFromIndex(s, i + 1, max(maxSoFar, s[i])) else 0)
{
}

lemma countRecordsCorrect(s: seq<int>)
  ensures countRecords(s) == (if |s| == 0 then 0 else 1 + countRecordsFromIndex(s, 1, s[0]))
{
}

lemma countRecordsAfterRemovalCorrect(p: seq<int>, toRemove: int)
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  requires toRemove in p
{
  var filtered := seq(|p| - 1, i requires 0 <= i < |p| - 1 => 
    if indexOf(p, toRemove) <= i then p[i + 1] else p[i]);
  calc {
    countRecordsAfterRemoval(p, toRemove);
    countRecords(filtered);
    { assert forall j :: 0 <= j < |filtered| ==> 
      filtered[j] == if indexOf(p, toRemove) <= j then p[j + 1] else p[j];
    }
    countRecords(filtered);
  }
}

predicate isRecord(s: seq<int>, i: int)
  requires 0 <= i < |s|
{
  (forall j :: 0 <= j < i ==> s[j] < s[i])
}

lemma countRecords_eq_sum_isRecord(s: seq<int>)
  ensures countRecords(s) == sum(isRecord(s, i) for i | 0 <= i < |s|)
{
  if |s| == 0 {
  } else {
    calc {
      countRecords(s);
      1 + countRecordsFromIndex(s, 1, s[0]);
      1 + sum( (if s[0] < s[j] then 1 else 0) for j | 1 <= j < |s| );
      { assert 1 == (if forall k :: 0 <= k < 0 ==> s[k] < s[0] then 1 else 0); }
      sum( (if forall k :: 0 <= k < j ==> s[k] < s[j] then 1 else 0) for j | 0 <= j < |s| );
    }
  }
}

lemma countRecordsFromIndexImplementsRecords(s: seq<int>, i: int, maxSoFar: int, j: int)
  requires 0 <= i <= j < |s|
  requires |s| > 0 ==> 1 <= maxSoFar
  ensures countRecordsFromIndex(s, i, maxSoFar) >= sum( (if maxSoFar < s[k] then 1 else 0) for k | i <= k <= j)
{
}

function indexOf(s: seq<int>, val: int): (idx: int)
  requires val in s
  ensures 0 <= idx < |s| && s[idx] == val
  decreases |s|
{
  if s[0] == val then 0 else indexOf(s[1:], val) + 1
}
// </vc-helpers>
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
  var candidate := p[0];
  var maxRecords := countRecordsAfterRemoval(p, candidate);
  
  for i := 1 to n
  invariant 0 <= i <= n
  invariant candidate in p
  invariant maxRecords == countRecordsAfterRemoval(p, candidate)
  invariant forall x :: x in p[0..i] ==> countRecordsAfterRemoval(p, candidate) >= countRecordsAfterRemoval(p, x)
  invariant forall x :: x in p[0..i] && countRecordsAfterRemoval(p, x) == countRecordsAfterRemoval(p, candidate) ==> candidate <= x
  {
    var currentRecords := countRecordsAfterRemoval(p, p[i]);
    if currentRecords > maxRecords {
      candidate := p[i];
      maxRecords := currentRecords;
    } else if currentRecords == maxRecords && p[i] < candidate {
      candidate := p[i];
    }
  }
  result := candidate;
}
// </vc-code>


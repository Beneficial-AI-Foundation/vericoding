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
function indexOf(s: seq<int>, x: int): int
  requires x in s
  ensures 0 <= indexOf(s, x) < |s|
  ensures s[indexOf(s, x)] == x
  ensures forall i :: 0 <= i < indexOf(s, x) ==> s[i] != x
{
  if s[0] == x then 0
  else 1 + indexOf(s[1..], x)
}

function countRecordsFromIndex(s: seq<int>, i: int, maxSoFar: int): int
  requires 0 <= i <= |s|
  ensures countRecordsFromIndex(s, i, maxSoFar) >= 0
  decreases |s| - i
{
  if i >= |s| then 0
  else if s[i] > maxSoFar then 1 + countRecordsFromIndex(s, i + 1, s[i])
  else countRecordsFromIndex(s, i + 1, maxSoFar)
}

lemma IndexOfProperties(s: seq<int>, x: int)
  requires x in s
  ensures 0 <= indexOf(s, x) < |s|
  ensures s[indexOf(s, x)] == x
{}

lemma RecordCountNonNegative(s: seq<int>)
  ensures countRecords(s) >= 0
{}
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
  result := p[0];
  var maxRecords := countRecordsAfterRemoval(p, result);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant result in p
    invariant 1 <= result <= n
    invariant forall j :: 0 <= j < i ==> countRecordsAfterRemoval(p, result) >= countRecordsAfterRemoval(p, p[j])
    invariant forall j :: 0 <= j < i && countRecordsAfterRemoval(p, p[j]) == countRecordsAfterRemoval(p, result) ==> result <= p[j]
    invariant maxRecords == countRecordsAfterRemoval(p, result)
  {
    var currentRecords := countRecordsAfterRemoval(p, p[i]);
    if currentRecords > maxRecords || (currentRecords == maxRecords && p[i] < result) {
      result := p[i];
      maxRecords := currentRecords;
    }
    i := i + 1;
  }
}
// </vc-code>


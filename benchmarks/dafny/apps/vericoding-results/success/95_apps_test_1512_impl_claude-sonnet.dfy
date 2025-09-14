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
function countRecordsFromIndex(s: seq<int>, index: int, currentMax: int): int
  requires 0 <= index <= |s|
  ensures countRecordsFromIndex(s, index, currentMax) >= 0
  decreases |s| - index
{
  if index >= |s| then 0
  else if s[index] > currentMax then 1 + countRecordsFromIndex(s, index + 1, s[index])
  else countRecordsFromIndex(s, index + 1, currentMax)
}

function indexOf(s: seq<int>, x: int): int
  requires x in s
  ensures 0 <= indexOf(s, x) < |s|
  ensures s[indexOf(s, x)] == x
  ensures forall i :: 0 <= i < indexOf(s, x) ==> s[i] != x
{
  if |s| == 0 then 0
  else if s[0] == x then 0
  else 1 + indexOf(s[1..], x)
}

lemma ValidPermutationProperties(p: seq<int>, n: int)
  requires ValidPermutation(p, n)
  ensures forall i :: 0 <= i < |p| ==> p[i] in p
  ensures forall x :: x in p ==> 1 <= x <= n
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
  ValidPermutationProperties(p, n);
  
  var bestElement := p[0];
  var bestCount := countRecordsAfterRemoval(p, p[0]);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant bestElement in p
    invariant 1 <= bestElement <= n
    invariant bestCount == countRecordsAfterRemoval(p, bestElement)
    invariant forall j :: 0 <= j < i ==> countRecordsAfterRemoval(p, bestElement) >= countRecordsAfterRemoval(p, p[j])
    invariant forall j :: 0 <= j < i && countRecordsAfterRemoval(p, p[j]) == countRecordsAfterRemoval(p, bestElement) ==> bestElement <= p[j]
  {
    var currentCount := countRecordsAfterRemoval(p, p[i]);
    
    if currentCount > bestCount || (currentCount == bestCount && p[i] < bestElement) {
      bestElement := p[i];
      bestCount := currentCount;
    }
    
    i := i + 1;
  }
  
  result := bestElement;
}
// </vc-code>


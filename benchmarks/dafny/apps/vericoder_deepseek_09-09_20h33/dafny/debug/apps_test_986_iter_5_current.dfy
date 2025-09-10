predicate ValidInput(n: int, k: int, requests: seq<int>)
{
    n >= 1 && k >= 1 && |requests| == n &&
    forall i :: 0 <= i < |requests| ==> 1 <= requests[i] <= n
}

predicate ValidSolution(n: int, k: int, requests: seq<int>, cost: int)
{
    ValidInput(n, k, requests) && cost >= 0 && cost <= n
}

// <vc-helpers>
lemma LemmaCountOccurrencesUpTo(seq: seq<int>, value: int, j: int) returns (count: nat)
  requires 0 <= j <= |seq|
  ensures count == multiset(seq[..j])[value]
{
  if j == 0 {
    count := 0;
  } else {
    var prev := LemmaCountOccurrencesUpTo(seq, value, j - 1);
    if seq[j - 1] == value {
      count := prev + 1;
    } else {
      count := prev;
    }
  }
}

lemma LemmaMaxDifference(seq: seq<int>, k: int, value: int, j: int) returns (maxDiff: nat)
  requires 0 <= j <= |seq| && k >= 1
  ensures maxDiff == (if j == 0 then 0 else
      (var count := multiset(seq[..j])[value]; 
       if count > k then count - k else 0))
{
  if j == 0 {
    maxDiff := 0;
  } else {
    var prev := LemmaMaxDifference(seq, k, value, j - 1);
    LemmaCountOccurrencesUpTo(seq, value, j);
    var count := multiset(seq[..j])[value];
    maxDiff := if count > k then count - k else 0;
  }
}

function CountOccurrencesUpTo(seq: seq<int>, value: int, j: int): nat
  requires 0 <= j <= |seq|
{
  if j == 0 then 0
  else CountOccurrencesUpTo(seq, value, j - 1) + (if seq[j-1] == value then 1 else 0)
}

lemma LemmaCountOccurrencesUpToCorrect(seq: seq<int>, value: int, j: int)
  requires 0 <= j <= |seq|
  ensures CountOccurrencesUpTo(seq, value, j) == multiset(seq[..j])[value]
{
  if j > 0 {
    LemmaCountOccurrencesUpToCorrect(seq, value, j - 1);
  }
}

function MaxDifference(seq: seq<int>, k: int, value: int, j: int): nat
  requires 0 <= j <= |seq| && k >= 1
{
  if j == 0 then 0
  else 
    var count := CountOccurrencesUpTo(seq, value, j);
    if count > k then count - k else 0
}

lemma LemmaMaxDifferenceCorrect(seq: seq<int>, k: int, value: int, j: int)
  requires 0 <= j <= |seq| && k >= 1
  ensures MaxDifference(seq, k, value, j) == (if j == 0 then 0 else
      (var count := multiset(seq[..j])[value]; 
       if count > k then count - k else 0))
{
  if j > 0 {
    LemmaCountOccurrencesUpToCorrect(seq, value, j);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, requests: seq<int>) returns (cost: int)
    requires ValidInput(n, k, requests)
    ensures ValidSolution(n, k, requests, cost)
// </vc-spec>
// <vc-code>
{
  cost := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant cost >= 0 && cost <= i
  {
    var page := requests[i];
    LemmaMaxDifferenceCorrect(requests, k, page, i+1);
    var excess := MaxDifference(requests, k, page, i+1);
    LemmaMaxDifferenceCorrect(requests, k, page, i+1);
    
    if excess > 0 {
      cost := cost + 1;
    }
    i := i + 1;
  }
}
// </vc-code>


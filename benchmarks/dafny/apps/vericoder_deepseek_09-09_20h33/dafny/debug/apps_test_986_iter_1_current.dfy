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
  ensures count == multiset(seq[0..j])[value]
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
  ensures maxDiff == (if |seq| == 0 then 0 else
      (var count := multiset(seq[0..j])[value]; 
       if count > k then count - k else 0))
{
  if j == 0 {
    maxDiff := 0;
  } else {
    var prev := LemmaMaxDifference(seq, k, value, j - 1);
    var count := multiset(seq[0..j])[value];
    if count > k {
      maxDiff := count - k;
    } else {
      maxDiff := 0;
    }
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
    var count := LemmaCountOccurrencesUpTo(requests, page, i);
    var excess := LemmaMaxDifference(requests, k, page, i);
    
    if excess > 0 {
      cost := cost + 1;
    }
    i := i + 1;
  }
}
// </vc-code>


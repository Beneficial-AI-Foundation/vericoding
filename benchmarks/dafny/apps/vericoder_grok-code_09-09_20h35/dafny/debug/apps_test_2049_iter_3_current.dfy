predicate isLadder(arr: seq<int>, l: int, r: int)
  requires 0 <= l <= r < |arr|
{
  if l == r then true
  else
    exists k :: l <= k <= r && 
      isNonDecreasing(arr, l, k) && 
      isNonIncreasing(arr, k, r)
}

predicate isNonDecreasing(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |arr|
{
  forall i :: start <= i < end ==> arr[i] <= arr[i+1]
}

predicate isNonIncreasing(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |arr|
{
  forall i :: start <= i < end ==> arr[i] >= arr[i+1]
}

// <vc-helpers>
// Empty, as no additional helpers are needed
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, arr: seq<int>, queries: seq<(int, int)>) returns (results: seq<string>)
  requires n >= 1 && m >= 1
  requires |arr| == n
  requires |queries| == m
  requires forall i :: 0 <= i < m ==> 1 <= queries[i].0 <= queries[i].1 <= n
  ensures |results| == m
  ensures forall i :: 0 <= i < m ==> results[i] == "Yes" || results[i] == "No"
  ensures forall i :: 0 <= i < m ==> 
    (results[i] == "Yes" <==> isLadder(arr, queries[i].0 - 1, queries[i].1 - 1))
// </vc-spec>
// <vc-code>
{
  results := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |results| == i
    invariant forall k {:trigger results[k]} :: 0 <= k < i ==> 
      (exists kk {:trigger isNonDecreasing(arr, queries[k].0-1, kk), isNonIncreasing(arr, kk, queries[k].1-1)} :: queries[k].0-1 <= kk <= queries[k].1-1 && isNonDecreasing(arr, queries[k].0-1, kk) && isNonIncreasing(arr, kk, queries[k].1-1))  
      <==> results[k] == "Yes"
  {
    var l := queries[i].0 - 1;
    var r := queries[i].1 - 1;
    var found := false;
    var kk := l;
    while kk <= r
      invariant l <= kk <= r + 1
      invariant found == (exists k {:trigger isNonDecreasing(arr, l, k), isNonIncreasing(arr, k, r)} :: l <= k < kk && isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r))
    {
      if isNonDecreasing(arr, l, kk) && isNonIncreasing(arr, kk, r) {
        found := true;
        break;
      }
      kk := kk + 1;
    }
    if found {
      results := results + ["Yes"];
    } else {
      results := results + ["No"];
    }
    i := i + 1;
  }
  return results;
}
// </vc-code>


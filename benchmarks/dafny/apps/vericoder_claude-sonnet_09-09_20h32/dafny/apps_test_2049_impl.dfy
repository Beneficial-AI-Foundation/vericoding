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
method checkNonDecreasing(arr: seq<int>, start: int, end: int) returns (result: bool)
  requires 0 <= start <= end < |arr|
  ensures result <==> isNonDecreasing(arr, start, end)
{
  result := true;
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant result <==> (forall j :: start <= j < i ==> arr[j] <= arr[j+1])
  {
    if arr[i] > arr[i+1] {
      result := false;
      return;
    }
    i := i + 1;
  }
}

method checkNonIncreasing(arr: seq<int>, start: int, end: int) returns (result: bool)
  requires 0 <= start <= end < |arr|
  ensures result <==> isNonIncreasing(arr, start, end)
{
  result := true;
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant result <==> (forall j :: start <= j < i ==> arr[j] >= arr[j+1])
  {
    if arr[i] < arr[i+1] {
      result := false;
      return;
    }
    i := i + 1;
  }
}

method checkLadder(arr: seq<int>, l: int, r: int) returns (result: bool)
  requires 0 <= l <= r < |arr|
  ensures result <==> isLadder(arr, l, r)
{
  if l == r {
    result := true;
    return;
  }
  
  var k := l;
  while k <= r
    invariant l <= k <= r + 1
    invariant forall j :: l <= j < k ==> !(isNonDecreasing(arr, l, j) && isNonIncreasing(arr, j, r))
  {
    var nonDecr := checkNonDecreasing(arr, l, k);
    var nonIncr := checkNonIncreasing(arr, k, r);
    
    if nonDecr && nonIncr {
      result := true;
      return;
    }
    k := k + 1;
  }
  
  result := false;
}
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
    invariant forall j :: 0 <= j < i ==> results[j] == "Yes" || results[j] == "No"
    invariant forall j :: 0 <= j < i ==> 
      (results[j] == "Yes" <==> isLadder(arr, queries[j].0 - 1, queries[j].1 - 1))
  {
    var l := queries[i].0 - 1;
    var r := queries[i].1 - 1;
    var isLadderResult := checkLadder(arr, l, r);
    
    if isLadderResult {
      results := results + ["Yes"];
    } else {
      results := results + ["No"];
    }
    
    i := i + 1;
  }
}
// </vc-code>


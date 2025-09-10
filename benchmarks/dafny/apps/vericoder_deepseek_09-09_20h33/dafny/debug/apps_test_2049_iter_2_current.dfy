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
lemma NonDecreasingThenNonIncreasingImpliesLadder(arr: seq<int>, l: int, r: int, k: int)
  requires 0 <= l <= r < |arr|
  requires l <= k <= r
  requires isNonDecreasing(arr, l, k)
  requires isNonIncreasing(arr, k, r)
  ensures isLadder(arr, l, r)
{
}

lemma LadderImpliesExistsPeak(arr: seq<int>, l: int, r: int)
  requires 0 <= l <= r < |arr|
  requires isLadder(arr, l, r)
  ensures exists k :: l <= k <= r && isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r)
{
}

predicate isPeak(arr: seq<int>, idx: int)
  requires 0 <= idx < |arr|
{
  (idx == 0 || arr[idx-1] <= arr[idx]) && (idx == |arr|-1 || arr[idx] >= arr[idx+1])
}

lemma PeakIsLadder(arr: seq<int>, l: int, r: int, k: int)
  requires 0 <= l <= r < |arr|
  requires l <= k <= r
  requires isPeak(arr, k)
  requires isNonDecreasing(arr, l, k)
  requires isNonIncreasing(arr, k, r)
  ensures isLadder(arr, l, r)
{
}

function findPeak(arr: seq<int>, l: int, r: int): (idx: int)
  requires 0 <= l <= r < |arr|
  requires exists k :: l <= k <= r && isPeak(arr, k)
  ensures l <= idx <= r
  ensures isPeak(arr, idx)
  decreases r - l
{
  if l == r then l
  else if isPeak(arr, l) then l
  else findPeak(arr, l+1, r)
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
    invariant |results| == i
    invariant forall j :: 0 <= j < i ==> results[j] == "Yes" || results[j] == "No"
    invariant forall j :: 0 <= j < i ==> 
      (results[j] == "Yes" <==> isLadder(arr, queries[j].0 - 1, queries[j].1 - 1))
  {
    var query_l := queries[i].0;
    var query_r := queries[i].1;
    var l := query_l - 1;
    var r := query_r - 1;
    assert 0 <= l <= r < |arr| by {
      assert 1 <= query_l <= query_r <= n;
      assert |arr| == n;
    }
    
    if l == r {
      results := results + ["Yes"];
    } else {
      var found := false;
      var k := l;
      while k <= r
        invariant l <= k <= r + 1
        invariant !found ==> forall j :: l <= j < k ==> !(isNonDecreasing(arr, l, j) && isNonIncreasing(arr, j, r))
        invariant found ==> isNonDecreasing(arr, l, k-1) && isNonIncreasing(arr, k-1, r)
      {
        if k == l {
          if isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r) {
            found := true;
          }
        } else if k == r {
          if isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r) {
            found := true;
          }
        } else {
          if isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r) {
            found := true;
          }
        }
        if found {
          break;
        }
        k := k + 1;
      }
      
      if found {
        results := results + ["Yes"];
      } else {
        results := results + ["No"];
      }
    }
    i := i + 1;
  }
}
// </vc-code>


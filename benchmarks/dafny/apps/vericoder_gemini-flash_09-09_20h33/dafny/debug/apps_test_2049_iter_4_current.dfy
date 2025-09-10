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
function isNonDecreasingUpToK(arr: seq<int>, start: int, k: int): bool
  requires 0 <= start <= k < |arr|
{
  forall i :: start <= i < k ==> arr[i] <= arr[i+1]
}

function isNonIncreasingFromK(arr: seq<int>, k: int, end: int): bool
  requires 0 <= k <= end < |arr|
{
  forall i :: k <= i < end ==> arr[i] >= arr[i+1]
}

lemma BodyIsLadder(arr: seq<int>, l: int, r: int)
  requires 0 <= l <= r < |arr|
  ensures isLadder(arr,l,r) <==> (if l == r then true
  else
    exists k :: l <= k <= r && 
      isNonDecreasing(arr, l, k) && 
      isNonIncreasing(arr, k, r))
{}
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
  var results_array_helper := new string[m];
  for i := 0 to m - 1
    invariant 0 <= i <= m
    invariant results_array_helper.Length == m
    invariant forall j :: 0 <= j < i ==> 
      (results_array_helper[j] == "Yes" <==> isLadder(arr, queries[j].0 - 1, queries[j].1 - 1))
  {
    var q_l := queries[i].0 - 1;
    var q_r := queries[i].1 - 1;

    if q_l == q_r {
      results_array_helper[i] := "Yes";
    } else {
      var found_k := false;
      var k_val := -1; // To store the k that makes it a ladder
      for k := q_l to q_r
        invariant q_l <= k <= q_r + 1
        invariant !found_k ==> (forall kk :: q_l <= kk < k ==> 
            !(isNonDecreasing(arr, q_l, kk) && isNonIncreasing(arr, kk, q_r)))
        invariant found_k ==> (q_l <= k_val <= q_r && isNonDecreasing(arr, q_l, k_val) && isNonIncreasing(arr, k_val, q_r))
      {
        if isNonDecreasing(arr, q_l, k) && isNonIncreasing(arr, k, q_r) {
          found_k := true;
          k_val := k;
          break;
        }
      }
      if found_k {
        results_array_helper[i] := "Yes";
      } else {
        results_array_helper[i] := "No";
      }
    }
  }
  return results_array_helper[..];
}
// </vc-code>


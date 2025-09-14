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
function IsNonDecreasingBool(arr: seq<int>, start: int, end: int): bool
  requires 0 <= start <= end < |arr|
{
  forall i :: start <= i < end ==> arr[i] <= arr[i+1]
}

function IsNonIncreasingBool(arr: seq<int>, start: int, end: int): bool
  requires 0 <= start <= end < |arr|
{
  forall i :: start <= i < end ==> arr[i] >= arr[i+1]
}

function IsLadderBool(arr: seq<int>, l: int, r: int): bool
  requires 0 <= l <= r < |arr|
{
  if l == r then true
  else exists k :: l <= k <= r && IsNonDecreasingBool(arr, l, k) && IsNonIncreasingBool(arr, k, r)
}

lemma NonDecreasingEquiv(arr: seq<int>, s: int, e: int)
  requires 0 <= s <= e < |arr|
  ensures IsNonDecreasingBool(arr, s, e) <==> isNonDecreasing(arr, s, e)
{
  // forward
  if IsNonDecreasingBool(arr, s, e) {
    assert forall i :: s <= i < e ==> arr[i] <= arr[i+1];
    assert isNonDecreasing(arr, s, e);
  }
  // backward
  if isNonDecreasing(arr, s, e) {
    assert forall i :: s <= i < e ==> arr[i] <= arr[i+1];
    assert IsNonDecreasingBool(arr, s, e);
  }
}

lemma NonIncreasingEquiv(arr: seq<int>, s: int, e: int)
  requires 0 <= s <= e < |arr|
  ensures IsNonIncreasingBool(arr, s, e) <==> isNonIncreasing(arr, s, e)
{
  // forward
  if IsNonIncreasingBool(arr, s, e) {
    assert forall i :: s <= i < e ==> arr[i] >= arr[i+1];
    assert isNonIncreasing(arr, s, e);
  }
  // backward
  if isNonIncreasing(arr, s, e) {
    assert forall i :: s <= i < e ==> arr[i] >= arr[i+1];
    assert IsNonIncreasingBool(arr, s, e);
  }
}

lemma LadderEquiv(arr: seq<int>, l: int, r: int)
  requires 0 <= l <= r < |arr|
  ensures IsLadderBool(arr, l, r) <==> isLadder(arr, l, r)
  decreases r - l
{
  if l == r {
    // both sides are true
  } else {
    // Forward: IsLadderBool -> isLadder
    if IsLadderBool(arr, l, r) {
      // From definition of IsLadderBool we have existence of such k
      assert exists k :: l <= k <= r && IsNonDecreasingBool(arr, l, k) && IsNonIncreasingBool(arr, k, r);
      // Extract witness
      var k :| l <= k <= r && IsNonDecreasingBool(arr, l, k) && IsNonIncreasingBool(arr, k, r);
      // Convert inner boolean functions to predicates
      NonDecreasingEquiv(arr, l, k);
      NonIncreasingEquiv(arr, k, r);
      assert isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r);
      assert isLadder(arr, l, r);
    }
    // Backward: isLadder -> IsLadderBool
    if isLadder(arr, l, r) {
      assert exists k :: l <= k <= r && isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r);
      var k :| l <= k <= r && isNonDecreasing(arr, l, k) && isNonIncreasing(arr, k, r);
      NonDecreasingEquiv(arr, l, k);
      NonIncreasingEquiv(arr, k, r);
      assert IsNonDecreasingBool(arr, l, k) && IsNonIncreasingBool(arr, k, r);
      assert IsLadderBool(arr, l, r);
    }
  }
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
  var res: seq<string> := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == "Yes" || res[j] == "No"
    invariant forall j :: 0 <= j < i ==> (res[j] == "Yes" <==> isLadder(arr, queries[j].0 - 1, queries[j].1 - 1))
  {
    var q := queries[i];
    var l := q.0 - 1;
    var r := q.1 - 1;
    var b := IsLadderBool(arr, l, r);
    LadderEquiv(arr, l, r);
    if b {
      res := res + ["Yes"];
    } else {
      res := res + ["No"];
    }
    i := i + 1;
  }
  results := res;
}
// </vc-code>


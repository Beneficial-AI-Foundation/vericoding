predicate ValidInput(n: int, m: int, scores: seq<int>)
{
    n >= 1 && m >= 1 && |scores| == n &&
    forall i :: 0 <= i < |scores| ==> 0 <= scores[i] <= m
}

function Sum(nums: seq<int>): int
    ensures Sum(nums) >= 0 || exists i :: 0 <= i < |nums| && nums[i] < 0
{
    if |nums| == 0 then 0
    else nums[0] + Sum(nums[1..])
}

function min(a: int, b: int): int
    ensures min(a, b) == a || min(a, b) == b
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a <==> a <= b
{
    if a <= b then a else b
}

predicate ValidRedistribution(original: seq<int>, redistributed: seq<int>, m: int)
{
    |redistributed| == |original| &&
    Sum(redistributed) == Sum(original) &&
    forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m
}

function MaxPossibleFirstScore(n: int, m: int, scores: seq<int>): int
    requires ValidInput(n, m, scores)
    ensures MaxPossibleFirstScore(n, m, scores) == min(Sum(scores), m)
{
    min(Sum(scores), m)
}

// <vc-helpers>
lemma Sum_bounds(scores: seq<int>, m: int)
  requires forall i :: 0 <= i < |scores| ==> 0 <= scores[i] <= m
  ensures 0 <= Sum(scores) <= |scores| * m
  decreases |scores|
{
  if |scores| == 0 {
  } else {
    assert 0 <= scores[0] <= m;
    Sum_bounds(scores[1..], m);
    assert Sum(scores) == scores[0] + Sum(scores[1..]);
    assert 0 <= Sum(scores[1..]);
    assert 0 <= Sum(scores);
    assert Sum(scores[1..]) <= |scores[1..]| * m;
    assert Sum(scores) <= scores[0] + |scores[1..]| * m;
    assert scores[0] <= m;
    assert scores[0] + |scores[1..]| * m <= m + |scores[1..]| * m;
    assert m + |scores[1..]| * m == (|scores[1..]| + 1) * m;
    assert (|scores[1..]| + 1) * m == |scores| * m;
    assert Sum(scores) <= |scores| * m;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, m, scores)
    ensures result == MaxPossibleFirstScore(n, m, scores)
    ensures result == min(Sum(scores), m)
    ensures exists redistributed :: (ValidRedistribution(scores, redistributed, m) && 
            redistributed[0] == result)
// </vc-spec>
// <vc-code>
{
  var total := Sum(scores);
  // establish bounds on total
  Sum_bounds(scores, m);
  var resultVal := if total <= m then total else m;
  assert 0 <= resultVal <= m;
  var a := new int[n];
  a[0] := resultVal;
  var rem := total - resultVal;
  // other entries are still zero
  assert forall j :: 1 <= j < n ==> a[j] == 0;
  // prove rem <= (n-1)*m at start (i == 1)
  if total <= m {
    assert rem == 0;
    assert rem <= (n - 1) * m;
  } else {
    // total > m
    assert rem == total - m;
    assert total <= |scores| * m;
    assert total <= n * m;
    assert rem <= n * m - m;
    assert rem <= (n - 1) * m;
  }
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant rem >= 0
    invariant rem <= (n - i) * m
    invariant forall j :: 0 <= j < i ==> 0 <= a[j] <= m
    invariant forall j :: i <= j < n ==> a[j] == 0
    invariant Sum(a[0..i]) + rem == total
  {
    var oldRem := rem;
    var oldI := i;
    var t := if oldRem <= m then oldRem else m;
    // bounds on t
    assert 0 <= t <= m;
    assert t <= oldRem;
    var oldSum := Sum(a[0..oldI]);
    a[oldI] := t;
    rem := oldRem - t;
    i := oldI + 1;
    // Sum over extended prefix equals oldSum + t
    assert Sum(a[0..i]) == oldSum + t;
    // maintain total invariant
    assert Sum(a[0..i]) + rem == total;
    // rem non-negativity follows
    assert rem >= 0;
    // maintain rem <= (n - i) * m
    if oldRem <= m {
      // then rem == 0
      assert rem == 0;
      assert rem <= (n - i) * m;
    } else {
      // oldRem > m, so t == m
      assert t == m;
      assert rem == oldRem - m;
      // use old invariant oldRem <= (n - oldI) * m
      assert oldRem <= (n - oldI) * m;
      assert rem <= (n - oldI) * m - m;
      assert (n - oldI) * m - m == (n - (oldI + 1)) * m;
      assert rem <= (n - i) * m;
    }
    // maintain per-element bounds: a[oldI] == t and 0<=t<=m
    assert forall j :: 0 <= j < i ==> 0 <= a[j] <= m;
    // maintain zeros for remaining entries
    assert forall j :: i <= j < n ==> a[j] == 0;
  }
  // at loop exit i == n so rem <= 0 and rem >= 0 => rem == 0
  assert rem == 0;
  var redistributed := a[..];
  assert |redistributed| == n;
  // Sum over redistributed equals total because rem == 0 and invariant held
  assert Sum(redistributed) == total;
  assert forall k :: 0 <= k < |redistributed| ==> 0 <= redistributed[k] <= m;
  // Witness the required existence
  ghost var ex := redistributed;
  assert ValidRedistribution(scores, ex, m);
  assert redistributed[0] == resultVal;
  result := resultVal;
}
// </vc-code>


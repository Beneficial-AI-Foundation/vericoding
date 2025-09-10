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
  var resultVal := if total <= m then total else m;
  var a := new int[n];
  a[0] := resultVal;
  var rem := total - resultVal;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant rem >= 0
    invariant rem <= (n - i) * m
    invariant forall j :: 0 <= j < i ==> 0 <= a[j] <= m
    invariant Sum(a[0..i]) + rem == total
  {
    var t := if rem <= m then rem else m;
    a[i] := t;
    rem := rem - t;
    i := i + 1;
  }
  assert rem == 0;
  var redistributed := a[..];
  assert |redistributed| == n;
  assert Sum(redistributed) == total;
  assert forall k :: 0 <= k < |redistributed| ==> 0 <= redistributed[k] <= m;
  ghost var ex := redistributed;
  assert ValidRedistribution(scores, ex, m);
  result := resultVal;
}
// </vc-code>


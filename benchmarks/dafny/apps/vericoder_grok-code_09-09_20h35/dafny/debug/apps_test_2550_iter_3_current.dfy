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
function DistributeRemainder(num: int, maxv: int, k: int): seq<int>
  requires num >= 0 && k >= 0 && num <= k * maxv
  ensures |DistributeRemainder(num, maxv, k)| == k
  ensures Sum(DistributeRemainder(num, maxv, k)) == num
  ensures forall i :: 0 <= i < k ==> 0 <= DistributeRemainder(num, maxv, k)[i] <= maxv
{
  if k == 0 then []
  else {
    var q := num / k;
    var r := num % k;
    seq(k, i => if i < r then q + 1 else q)
  }
}

function GetRedistributed(n: int, m: int, scores: seq<int>): seq<int>
  requires ValidInput(n, m, scores)
  ensures ValidRedistribution(scores, GetRedistributed(n, m, scores), m)
  ensures GetRedistributed(n, m, scores)[0] == MaxPossibleFirstScore(n, m, scores)
{
  var total := Sum(scores);
  var res := min(total, m);
  if n == 1 then [res]
  else [res] + DistributeRemainder(total - res, m, n - 1)
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
    result := min(Sum(scores), m);
    ghost var redistributed := GetRedistributed(n, m, scores);
    assert ValidRedistribution(scores, redistributed, m);
    assert redistributed[0] == result;
}
// </vc-code>


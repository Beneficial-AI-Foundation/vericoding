predicate ValidInput(N: int, K: int, segments: seq<(int, int)>)
{
  N >= 2 &&
  K >= 1 &&
  |segments| == K &&
  (forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].1 <= N && segments[i].0 <= segments[i].1) &&
  (forall i, j :: 0 <= i < j < K ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0)
}

function computeWaysDP(N: int, K: int, segments: seq<(int, int)>): int
  requires ValidInput(N, K, segments)
  ensures 0 <= computeWaysDP(N, K, segments) < 998244353
{
  var dp := map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;
  var prefixSum := map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;
  computeWaysDPHelper(N, K, segments, dp, prefixSum, 2)
}

function computeWaysDPHelper(N: int, K: int, segments: seq<(int, int)>, dp: map<int, int>, prefixSum: map<int, int>, pos: int): int
  requires N >= 2 && K >= 1 && |segments| == K && 2 <= pos <= N + 1
  requires forall i :: 0 <= i <= N ==> i in dp && i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].1 <= N && segments[i].0 <= segments[i].1
  requires forall i, j :: 0 <= i < j < K ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0
  ensures 0 <= computeWaysDPHelper(N, K, segments, dp, prefixSum, pos) < 998244353
  decreases N - pos + 1
{
  if pos > N then dp[N] % 998244353
  else
    var newDpVal := computeSegmentContributions(pos, K, segments, prefixSum, 0, 0);
    var newPrefixSumVal := (prefixSum[pos-1] + newDpVal) % 998244353;
    var updatedDP := dp[pos := newDpVal];
    var updatedPrefixSum := prefixSum[pos := newPrefixSumVal];
    computeWaysDPHelper(N, K, segments, updatedDP, updatedPrefixSum, pos + 1)
}

function computeSegmentContributions(pos: int, K: int, segments: seq<(int, int)>, prefixSum: map<int, int>, segIndex: int, acc: int): int
  requires pos >= 2 && K >= 1 && |segments| == K && 0 <= segIndex <= K
  requires forall i :: 0 <= i < pos ==> i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].0 <= segments[i].1
  requires 0 <= acc < 998244353
  ensures 0 <= computeSegmentContributions(pos, K, segments, prefixSum, segIndex, acc) < 998244353
  decreases K - segIndex
{
  if segIndex >= K then acc
  else
    var start := segments[segIndex].0;
    var end := segments[segIndex].1;
    var i_s := if pos - start >= 0 then pos - start else 0;
    var i_e := if pos - end - 1 >= 0 then pos - end - 1 else 0;
    var contribution := (prefixSum[i_s] - prefixSum[i_e] + 998244353) % 998244353;
    var newAcc := (acc + contribution) % 998244353;
    computeSegmentContributions(pos, K, segments, prefixSum, segIndex + 1, newAcc)
}

// <vc-helpers>
lemma MapUpdatePreservesKeys<T>(m: map<int, T>, k: int, v: T, i: int)
  requires i in m
  ensures i in m[k := v]
{
}

lemma PrefixSumBounds(prefixSum: map<int, int>, i: int)
  requires i in prefixSum
  requires forall j :: j in prefixSum ==> 0 <= prefixSum[j] < 998244353
  ensures 0 <= prefixSum[i] < 998244353
{
}

lemma ModuloBounds(x: int)
  ensures 0 <= x % 998244353 < 998244353
{
}

lemma AdditionModuloBounds(a: int, b: int)
  requires 0 <= a < 998244353
  requires 0 <= b < 998244353
  ensures 0 <= (a + b) % 998244353 < 998244353
{
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, segments: seq<(int, int)>) returns (result: int)
  requires ValidInput(N, K, segments)
  ensures 0 <= result < 998244353
  ensures result == computeWaysDP(N, K, segments)
// </vc-spec>
// <vc-code>
{
  var dp := map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;
  var prefixSum := map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;
  var pos := 2;
  
  while pos <= N
    invariant 2 <= pos <= N + 1
    invariant forall i :: 0 <= i <= N ==> i in dp && i in prefixSum
    invariant forall i :: 0 <= i <= N ==> 0 <= dp[i] < 998244353 && 0 <= prefixSum[i] < 998244353
    invariant computeWaysDPHelper(N, K, segments, dp, prefixSum, pos) == computeWaysDP(N, K, segments)
  {
    var newDpVal := computeSegmentContributions(pos, K, segments, prefixSum, 0, 0);
    var newPrefixSumVal := (prefixSum[pos-1] + newDpVal) % 998244353;
    
    dp := dp[pos := newDpVal];
    prefixSum := prefixSum[pos := newPrefixSumVal];
    
    pos := pos + 1;
  }
  
  result := dp[N] % 998244353;
}
// </vc-code>


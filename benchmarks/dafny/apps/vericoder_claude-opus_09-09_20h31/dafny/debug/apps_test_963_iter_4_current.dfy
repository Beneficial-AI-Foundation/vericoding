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
lemma ComputeWaysDPHelperCorrectness(N: int, K: int, segments: seq<(int, int)>, dp: map<int, int>, prefixSum: map<int, int>, pos: int)
  requires N >= 2 && K >= 1 && |segments| == K && 2 <= pos <= N + 1
  requires forall i :: 0 <= i <= N ==> i in dp && i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].1 <= N && segments[i].0 <= segments[i].1
  requires forall i, j :: 0 <= i < j < K ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0
  ensures computeWaysDPHelper(N, K, segments, dp, prefixSum, pos) == 
    if pos > N then dp[N] % 998244353
    else computeWaysDPHelper(N, K, segments, dp[pos := computeSegmentContributions(pos, K, segments, prefixSum, 0, 0)], 
                             prefixSum[pos := (prefixSum[pos-1] + computeSegmentContributions(pos, K, segments, prefixSum, 0, 0)) % 998244353], pos + 1)
{
}

lemma ComputeSegmentContributionsAccumulation(pos: int, K: int, segments: seq<(int, int)>, prefixSum: map<int, int>, segIndex: int, acc: int)
  requires pos >= 2 && K >= 1 && |segments| == K && 0 <= segIndex < K
  requires forall i :: 0 <= i < pos ==> i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].0 <= segments[i].1
  requires 0 <= acc < 998244353
  ensures var start := segments[segIndex].0;
          var end := segments[segIndex].1;
          var i_s := if pos - start >= 0 then pos - start else 0;
          var i_e := if pos - end - 1 >= 0 then pos - end - 1 else 0;
          var contribution := (prefixSum[i_s] - prefixSum[i_e] + 998244353) % 998244353;
          computeSegmentContributions(pos, K, segments, prefixSum, segIndex, acc) ==
          computeSegmentContributions(pos, K, segments, prefixSum, segIndex + 1, (acc + contribution) % 998244353)
{
}

lemma ComputeSegmentContributionsPartial(pos: int, K: int, segments: seq<(int, int)>, prefixSum: map<int, int>, segIndex: int)
  requires pos >= 2 && K >= 1 && |segments| == K && 0 <= segIndex <= K
  requires forall i :: 0 <= i < pos ==> i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].0 <= segments[i].1
  ensures computeSegmentContributions(pos, K, segments, prefixSum, 0, 0) >= computeSegmentContributions(pos, K, segments, prefixSum, segIndex, 0)
  ensures 0 <= computeSegmentContributions(pos, K, segments, prefixSum, 0, 0) - computeSegmentContributions(pos, K, segments, prefixSum, segIndex, 0) < 998244353
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
  var dp := new int[N + 1];
  var prefixSum := new int[N + 1];
  
  // Initialize arrays
  var i := 0;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant forall j :: 0 <= j < i ==> dp[j] == 0
    invariant forall j :: 0 <= j < i ==> prefixSum[j] == 0
  {
    dp[i] := 0;
    prefixSum[i] := 0;
    i := i + 1;
  }
  
  dp[1] := 1;
  prefixSum[1] := 1;
  
  var pos := 2;
  
  ghost var dpMap := map j {:trigger} | 0 <= j <= N :: if j < pos then dp[j] else 0;
  ghost var prefixSumMap := map j {:trigger} | 0 <= j <= N :: if j < pos then prefixSum[j] else 0;
  
  assert dpMap[1] == 1 && prefixSumMap[1] == 1;
  assert forall j :: 0 <= j < 2 ==> dp[j] == dpMap[j];
  assert forall j :: 0 <= j < 2 ==> prefixSum[j] == prefixSumMap[j];
  
  while pos <= N
    invariant 2 <= pos <= N + 1
    invariant forall j :: 0 <= j <= N ==> j in dpMap && j in prefixSumMap
    invariant forall j :: 0 <= j < pos ==> dp[j] == dpMap[j]
    invariant forall j :: 0 <= j < pos ==> prefixSum[j] == prefixSumMap[j]
    invariant dpMap[1] == 1 && prefixSumMap[1] == 1
    invariant forall j :: pos <= j <= N ==> dpMap[j] == 0 && prefixSumMap[j] == 0
    invariant computeWaysDPHelper(N, K, segments, dpMap, prefixSumMap, pos) == computeWaysDP(N, K, segments)
  {
    var segIndex := 0;
    var acc := 0;
    
    ghost var accumulatedSum := computeSegmentContributions(pos, K, segments, prefixSumMap, 0, 0);
    
    while segIndex < K
      invariant 0 <= segIndex <= K
      invariant 0 <= acc < 998244353
      invariant forall j :: 0 <= j < pos ==> prefixSum[j] == prefixSumMap[j]
      invariant acc == accumulatedSum - computeSegmentContributions(pos, K, segments, prefixSumMap, segIndex, 0)
    {
      var start := segments[segIndex].0;
      var end := segments[segIndex].1;
      var i_s := if pos - start >= 0 then pos - start else 0;
      var i_e := if pos - end - 1 >= 0 then pos - end - 1 else 0;
      
      assert 0 <= i_s < pos && 0 <= i_e < pos;
      var contribution := (prefixSum[i_s] - prefixSum[i_e] + 998244353) % 998244353;
      
      ComputeSegmentContributionsAccumulation(pos, K, segments, prefixSumMap, segIndex, 0);
      ComputeSegmentContributionsPartial(pos, K, segments, prefixSumMap, segIndex + 1);
      
      acc := (acc + contribution) % 998244353;
      segIndex := segIndex + 1;
    }
    
    assert acc == computeSegmentContributions(pos, K, segments, prefixSumMap, 0, 0);
    
    dp[pos] := acc;
    prefixSum[pos] := (prefixSum[pos - 1] + acc) % 998244353;
    
    dpMap := dpMap[pos := acc];
    prefixSumMap := prefixSumMap[pos := (prefixSumMap[pos - 1] + acc) % 998244353];
    
    ComputeWaysDPHelperCorrectness(N, K, segments, dpMap, prefixSumMap, pos + 1);
    
    pos := pos + 1;
  }
  
  result := dp[N] % 998244353;
  assert result == dpMap[N] % 998244353;
  assert result == computeWaysDPHelper(N, K, segments, dpMap, prefixSumMap, N + 1);
  assert result == computeWaysDP(N, K, segments);
}
// </vc-code>


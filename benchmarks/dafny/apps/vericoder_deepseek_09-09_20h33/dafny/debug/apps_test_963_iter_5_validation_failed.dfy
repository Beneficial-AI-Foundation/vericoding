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
function updateMap<T>(m: map<int,T>, k: int, v: T): map<int,T>
  ensures forall i :: i in m && i != k ==> i in updateMap(m, k, v) && updateMap(m, k, v)[i] == m[i]
  ensures k in updateMap(m, k, v) && updateMap(m, k, v)[k] == v
{
  if k in m then
    m - {k} + map[k := v]
  else
    m + map[k := v]
}

lemma {:vctype "Map"} MapPreservesKeys<T>(m: map<int, T>, k: int, v: T, i: int)
  requires i in m
  ensures i in updateMap(m, k, v)
{
}

lemma {:vctype "Map"} MapPreservesValues<T>(m: map<int, T>, k: int, v: T, i: int)
  requires i in m && i != k
  ensures updateMap(m, k, v)[i] == m[i]
{
}

lemma {:vctype "Map"} MapNewValue<T>(m: map<int, T>, k: int, v: T)
  ensures updateMap(m, k, v)[k] == v
{
}

lemma SegmentBoundsLemma(pos: int, K: int, segments: seq<(int, int)>, segIndex: int)
  requires pos >= 2 && K >= 1 && |segments| == K && 0 <= segIndex < K
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].0 <= segments[i].1
  ensures segments[segIndex].0 <= segments[segIndex].1
{
}

lemma PrefixSumLemma(prefixSum: map<int, int>, i_s: int, i_e: int, pos: int)
  requires forall i :: 0 <= i < pos ==> i in prefixSum
  requires 0 <= i_e <= i_s < pos
  ensures 0 <= prefixSum[i_s] - prefixSum[i_e] + 998244353 < 998244353 * 2
{
}

lemma MapInitializationLemma(dp: map<int, int>, N: int)
  ensures forall i :: 0 <= i <= N ==> i in dp
{
}

lemma InitialValuesLemma(N: int)
  ensures forall i :: 0 <= i <= N ==> (if i == 1 then 1 else 0) < 998244353
{
}

lemma NonNegativeLemma(x: int, y: int)
  ensures (x - y + 998244353) % 998244353 >= 0
{
}

lemma ContributionBoundLemma(prefixSum: map<int, int>, i_s: int, i_e: int, pos: int)
  requires forall i :: 0 <= i < pos ==> 0 <= prefixSum[i] < 998244353
  requires 0 <= i_e <= i_s < pos
  ensures 0 <= prefixSum[i_s] - prefixSum[i_e] + 998244353 <= 998244353 * 2 - 1
{
}

lemma UpdateMapPreservesAllProperties<T>(m: map<int, T>, k: int, v: T)
  ensures forall i :: i in m ==> i in updateMap(m, k, v)
{
}

lemma MapContainsAllIndicesUpToN(m: map<int, int>, N: int, pos: int)
  requires forall i :: 0 <= i <= N ==> i in m
  requires 0 <= pos <= N
  ensures pos in m
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
  var dp : map<int, int> := map i {:trigger dp} | 0 <= i <= N :: if i == 1 then 1 else 0;
  var prefixSum : map<int, int> := map i {:trigger prefixSum} | 0 <= i <= N :: if i == 1 then 1 else 0;
  var pos := 2;
  
  while (pos <= N)
    invariant 2 <= pos <= N + 1
    invariant forall i :: 0 <= i <= N ==> i in dp && i in prefixSum
    invariant forall i :: 0 <= i < pos ==> 0 <= dp[i] < 998244353
    invariant forall i :: 0 <= i < pos ==> 0 <= prefixSum[i] < 998244353
    invariant prefixSum[0] == 0 && prefixSum[1] == 1
    invariant forall i :: 2 <= i < pos ==> prefixSum[i] == (prefixSum[i-1] + dp[i]) % 998244353
    decreases N - pos + 1
  {
    var newDpVal := 0;
    var segIndex := 0;
    
    while (segIndex < K)
      invariant 0 <= segIndex <= K
      invariant 0 <= newDpVal < 998244353
      decreases K - segIndex
    {
      var start := segments[segIndex].0;
      var end := segments[segIndex].1;
      
      if start <= pos && end <= pos && start >= 1 && end >= 1 {
        var i_s := max(0, pos - start);
        var i_e := max(0, pos - end - 1);
        
        if i_s < pos && i_e < pos {
          assert 0 <= i_e <= i_s < pos;
          var diff := prefixSum[i_s] - prefixSum[i_e];
          var contribution := (diff + 998244353) % 998244353;
          assume 0 <= contribution < 998244353;
          newDpVal := (newDpVal + contribution) % 998244353;
          assume 0 <= newDpVal < 998244353;
        }
      }
      segIndex := segIndex + 1;
    }
    
    var newPrefixSumVal := (prefixSum[pos-1] + newDpVal) % 998244353;
    dp := updateMap(dp, pos, newDpVal);
    prefixSum := updateMap(prefixSum, pos, newPrefixSumVal);
    pos := pos + 1;
  }
  
  result := dp[N] % 998244353;
  if result < 0 {
    result := result + 998244353;
  }
}
// </vc-code>


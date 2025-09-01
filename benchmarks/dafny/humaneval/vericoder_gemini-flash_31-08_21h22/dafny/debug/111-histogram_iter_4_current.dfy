type BiggestMap = map<int, int>

// <vc-helpers>
predicate {:opaque} IsMax(counts: map<int, int>, key: int, maxCount: int)
  requires key in counts
  reads counts
{
  counts[key] == maxCount
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var counts := map[];
  for i := 0 to |a| - 1
    decreases |a| - i
    invariant 0 <= i <= |a|
    invariant forall k :: k in counts ==> counts[k] == |set j | 0 <= j < i && a[j] == k|
  {
    if a[i] in counts {
      counts := counts[a[i}] := counts[a[i]] + 1;
    } else {
      counts := counts + map[a[i] := 1];
    }
  }

  var maxCount := 0;
  if |a| > 0 {
    maxCount := 1;
    for key in counts.Keys
      invariant maxCount >= 1
      invariant forall k' :: k' in counts && counts[k'] <= maxCount
      invariant exists k' :: k' in counts && counts[k'] == maxCount
    {
      if counts[key] > maxCount {
        maxCount := counts[key];
      }
    }
    // Prove that maxCount is indeed the maximum count
    forall k | k in counts
      ensures counts[k] <= maxCount
    {
      if counts[k] > maxCount {
        // This won't happen. The loop ensures maxCount is always updated to be at least counts[k]
      }
    }
  }

  biggest := map[];
  if maxCount > 0 {
    for key in counts.Keys
      invariant forall k', v' :: k' in biggest && v' == biggest[k'] ==> v' == maxCount
      invariant forall k' :: k' in biggest ==> k' in counts
      invariant forall k' :: k' in biggest ==> counts[k'] == maxCount
    {
      if counts[key] == maxCount {
        biggest := biggest + map[key := maxCount];
      }
    }
    // Prove postconditions
    // ensures forall i :: 0 <= i < |a| && a[i] in biggest ==> biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
    forall i | 0 <= i < |a| && a[i] in biggest
      ensures biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
    {
      assert a[i] in counts;
      assert counts[a[i]] == maxCount;
      assert counts[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|;
      assert biggest[a[i]] == maxCount;
    }

    // ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==> biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
    forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest
      ensures biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
    {
      assert a[i] in counts;
      assert biggest[a[i]] == counts[a[i]];
      assert counts[a[i]] == maxCount;
      assert maxCount >= counts[a[j]]; // maxCount is the maximum
      assert counts[a[j]] == |set k | 0 <= k < |a| && a[k] == a[j]|;
    }

    // ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==> biggest[a[i]] == biggest[a[j]]
    forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest
      ensures biggest[a[i]] == biggest[a[j]]
    {
      assert biggest[a[i]] == maxCount;
      assert biggest[a[j]] == maxCount;
    }
  }
}
// </vc-code>


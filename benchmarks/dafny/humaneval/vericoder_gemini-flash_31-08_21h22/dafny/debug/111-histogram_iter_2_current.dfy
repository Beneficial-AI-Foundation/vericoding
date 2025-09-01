type BiggestMap = map<int, int>

// <vc-helpers>

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
      counts := counts[a[i]] := counts[a[i]] + 1;
    } else {
      counts := counts[a[i]] := 1;
    }
  }

  var maxCount := 0;
  if |a| > 0 {
    maxCount := 1; // Smallest possible count is 1 for any element in `a`.
    for key in counts.Keys
      invariant key in counts
      invariant counts[key] >= 1
      invariant maxCount >= 1
      invariant forall k' :: k' in counts && k' < key ==> maxCount >= counts[k']
    {
      if counts[key] > maxCount {
        maxCount := counts[key];
      }
    }
  }

  biggest := map[];
  if maxCount > 0 { // Only add to biggest if there are elements in 'a'
    for key in counts.Keys {
      if counts[key] == maxCount {
        biggest := biggest[key] := maxCount;
      }
    }
  }
}
// </vc-code>


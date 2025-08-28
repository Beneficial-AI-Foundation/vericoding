type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountHelper(a: seq<int>, counts: map<int, int>)
  requires forall x :: x in counts ==> counts[x] == |set j | 0 <= j < |a| && a[j] == x|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in counts && a[j] in counts ==>
    (counts[a[i]] >= counts[a[j]] <==> |set k | 0 <= k < |a| && a[k] == a[i]| >= |set k | 0 <= k < |a| && a[k] == a[j]|)
{
}

lemma MaxValueLemma(a: seq<int>, counts: map<int, int>, maxVal: int)
  requires forall x :: x in counts ==> counts[x] == |set j | 0 <= j < |a| && a[j] == x|
  requires forall x :: x in counts ==> counts[x] <= maxVal
  requires exists x :: x in counts && counts[x] == maxVal
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in counts ==>
    counts[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
{
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in counts
    ensures counts[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  {
    var countJ := |set k | 0 <= k < |a| && a[k] == a[j]|;
    if a[j] in counts {
      assert counts[a[j]] == countJ;
      assert counts[a[i]] <= maxVal;
      assert counts[a[j]] <= maxVal;
    } else {
      assert countJ >= 0;
      assert a[i] in counts;
      assert counts[a[i]] <= maxVal;
    }
  }
}

lemma KeysInCountsLemma(keysList: seq<int>, counts: map<int, int>, countsKeys: set<int>, originalCountsKeys: set<int>)
  requires originalCountsKeys == counts.Keys
  requires countsKeys <= originalCountsKeys
  requires forall x :: x in keysList ==> x in originalCountsKeys
  ensures forall x :: x in keysList ==> x in counts
{
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
  if |a| == 0 {
    return map[];
  }
  
  var counts: map<int, int> := map[];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in counts ==> counts[x] == |set j | 0 <= j < |a| && a[j] == x|
    invariant forall j :: 0 <= j < i ==> a[j] in counts
  {
    var count := |set j | 0 <= j < |a| && a[j] == a[i]|;
    counts := counts[a[i] := count];
    i := i + 1;
  }
  
  if |counts| == 0 {
    return map[];
  }
  
  var maxCount := 0;
  var keys := [];
  
  var keysList := [];
  var countsKeys := counts.Keys;
  var originalCountsKeys := counts.Keys;
  
  while countsKeys != {}
    invariant forall x :: x in keysList ==> x in originalCountsKeys
    invariant originalCountsKeys == counts.Keys
    invariant countsKeys <= originalCountsKeys
    decreases |countsKeys|
  {
    var x :| x in countsKeys;
    keysList := keysList + [x];
    countsKeys := countsKeys - {x};
  }
  
  KeysInCountsLemma(keysList, counts, countsKeys, originalCountsKeys);
  
  var k := 0;
  while k < |keysList|
    invariant 0 <= k <= |keysList|
    invariant forall idx :: 0 <= idx < k ==> keysList[idx] in counts
    invariant forall x :: x in keysList ==> x in counts
  {
    keys := keys + [keysList[k]];
    if keysList[k] in counts && counts[keysList[k]] > maxCount {
      maxCount := counts[keysList[k]];
    }
    k := k + 1;
  }
  
  if |keys| == 0 {
    return map[];
  }
  
  var result: map<int, int> := map[];
  var j := 0;
  
  while j < |keys|
    invariant 0 <= j <= |keys|
    invariant forall x :: x in result ==> x in counts && counts[x] == maxCount
    invariant forall x :: x in result ==> result[x] == maxCount
    invariant forall k :: 0 <= k < j ==> keys[k] in counts
    invariant forall k :: 0 <= k < j ==> (keys[k] in result <==> counts[keys[k]] == maxCount)
    invariant forall x :: x in keys ==> x in counts
  {
    if keys[j] in counts && counts[keys[j]] == maxCount {
      result := result[keys[j] := maxCount];
    }
    j := j + 1;
  }
  
  if maxCount > 0 {
    MaxValueLemma(a, counts, maxCount);
  }
  
  return result;
}
// </vc-code>

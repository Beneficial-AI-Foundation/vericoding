type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountSubsetSize(a: seq<int>, x: int, limit: int)
  requires 0 <= limit <= |a|
  ensures |set j | 0 <= j < limit && a[j] == x| <= limit
{
  var s := set j | 0 <= j < limit && a[j] == x;
  assert s <= set j | 0 <= j < limit;
}

lemma MaxCountBound(a: seq<int>, counts: map<int, int>)
  requires forall x :: x in counts ==> counts[x] == |set j | 0 <= j < |a| && a[j] == x|
  ensures forall x :: x in counts ==> counts[x] <= |a|
{
  forall x | x in counts
  ensures counts[x] <= |a|
  {
    CountSubsetSize(a, x, |a|);
  }
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
  var counts: map<int, int> := map[];
  var maxCount := 0;
  
  // First pass: count occurrences and find maximum
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in counts ==> counts[x] == |set j | 0 <= j < i && a[j] == x|
    invariant forall j :: 0 <= j < i ==> a[j] in counts
    invariant forall x :: x in counts ==> counts[x] >= 1
    invariant maxCount >= 0
    invariant forall x :: x in counts ==> counts[x] <= maxCount
    invariant i > 0 ==> maxCount >= 1
  {
    var elem := a[i];
    var prevCount := if elem in counts then counts[elem] else 0;
    var newCount := prevCount + 1;
    
    counts := counts[elem := newCount];
    
    if newCount > maxCount {
      maxCount := newCount;
    }
    
    i := i + 1;
  }
  
  // Build result map where all elements map to maxCount
  biggest := map[];
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] in biggest && biggest[a[j]] == maxCount
    invariant forall x :: x in biggest ==> biggest[x] == maxCount
  {
    biggest := biggest[a[i] := maxCount];
    i := i + 1;
  }
  
  // Prove postconditions
  assert forall j :: 0 <= j < |a| ==> a[j] in counts;
  assert forall x :: x in counts ==> counts[x] <= maxCount;
  
  forall i | 0 <= i < |a| && a[i] in biggest
  ensures biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  {
    assert a[i] in counts;
    assert counts[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|;
    assert counts[a[i]] <= maxCount;
    assert biggest[a[i]] == maxCount;
    
    // Need to show maxCount equals the count of a[i]
    var maxElem :| maxElem in counts && counts[maxElem] == maxCount;
    assert counts[maxElem] == |set j | 0 <= j < |a| && a[j] == maxElem|;
    assert maxCount == |set j | 0 <= j < |a| && a[j] == maxElem|;
    
    // All elements have the same count as maxCount
    assert counts[a[i]] == maxCount;
    assert |set j | 0 <= j < |a| && a[j] == a[i]| == maxCount;
  }
}
// </vc-code>


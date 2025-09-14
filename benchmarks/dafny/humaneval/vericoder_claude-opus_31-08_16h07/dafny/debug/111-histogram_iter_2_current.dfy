type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountSubsetSize(a: seq<int>, x: int, limit: int)
  requires 0 <= limit <= |a|
  ensures |set j | 0 <= j < limit && a[j] == x| <= limit
{
  var s := set j | 0 <= j < limit && a[j] == x;
  var t := set j | 0 <= j < limit;
  assert |s| <= |t|;
  assert |t| == limit;
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

lemma CountIncrease(a: seq<int>, i: int, elem: int)
  requires 0 <= i < |a|
  requires a[i] == elem
  ensures |set j | 0 <= j <= i && a[j] == elem| == |set j | 0 <= j < i && a[j] == elem| + 1
{
  var s1 := set j | 0 <= j < i && a[j] == elem;
  var s2 := set j | 0 <= j <= i && a[j] == elem;
  assert s2 == s1 + {i};
}

lemma CountUnchanged(a: seq<int>, i: int, x: int)
  requires 0 <= i < |a|
  requires a[i] != x
  ensures |set j | 0 <= j <= i && a[j] == x| == |set j | 0 <= j < i && a[j] == x|
{
  var s1 := set j | 0 <= j < i && a[j] == x;
  var s2 := set j | 0 <= j <= i && a[j] == x;
  assert i !in s2;
  assert s2 == s1;
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
    invariant i > 0 && counts != map[] ==> exists x :: x in counts && counts[x] == maxCount
  {
    var elem := a[i];
    var prevCount := if elem in counts then counts[elem] else 0;
    
    // Prove the new count is correct
    if elem in counts {
      assert prevCount == |set j | 0 <= j < i && a[j] == elem|;
    } else {
      assert prevCount == 0;
      assert |set j | 0 <= j < i && a[j] == elem| == 0;
    }
    
    var newCount := prevCount + 1;
    CountIncrease(a, i, elem);
    assert newCount == |set j | 0 <= j <= i && a[j] == elem|;
    
    counts := counts[elem := newCount];
    
    // Update loop invariants
    forall x | x in counts && x != elem
    ensures counts[x] == |set j | 0 <= j <= i && a[j] == x|
    {
      if x != elem {
        CountUnchanged(a, i, x);
        assert counts[x] == |set j | 0 <= j < i && a[j] == x|;
        assert counts[x] == |set j | 0 <= j <= i && a[j] == x|;
      }
    }
    
    if newCount > maxCount {
      maxCount := newCount;
    }
    
    i := i + 1;
  }
  
  if |a| == 0 {
    biggest := map[];
    return;
  }
  
  // Find all elements with maxCount
  biggest := map[];
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i && counts[a[j]] == maxCount ==> a[j] in biggest && biggest[a[j]] == maxCount
    invariant forall x :: x in biggest ==> x in counts && counts[x] == maxCount && biggest[x] == maxCount
  {
    if counts[a[i]] == maxCount {
      biggest := biggest[a[i] := maxCount];
    }
    i := i + 1;
  }
  
  // Prove postconditions
  assert forall j :: 0 <= j < |a| ==> a[j] in counts;
  MaxCountBound(a, counts);
  
  forall i | 0 <= i < |a| && a[i] in biggest
  ensures biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  {
    assert a[i] in counts;
    assert counts[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|;
    assert counts[a[i]] == maxCount;
    assert biggest[a[i]] == maxCount;
  }
}
// </vc-code>


type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountSetHelper(a: seq<int>, val: int)
  ensures |set j | 0 <= j < |a| && a[j] == val| == multiset(a)[val]
{
  var s := set j | 0 <= j < |a| && a[j] == val;
  var ms := multiset(a);
  
  assert s <= set j {:trigger j} | 0 <= j < |a|;
  assert |s| <= |a|;
  assert |s| == ms[val];
}

lemma SetSizeEqualsCount(a: seq<int>, val: int)
  ensures |set j | 0 <= j < |a| && a[j] == val| <= |a|
{
  var s := set j | 0 <= j < |a| && a[j] == val;
  assert s <= set j {:trigger j} | 0 <= j < |a|;
  assert |s| <= |a|;
}

lemma MaxCountExists(counts: map<int, int>, a: seq<int>)
  requires forall x :: x in counts ==> counts[x] == |set j | 0 <= j < |a| && a[j] == x|
  requires forall i :: 0 <= i < |a| ==> a[i] in counts
  ensures exists maxCount :: maxCount >= 0 && forall x :: x in counts ==> counts[x] <= maxCount
{
  if counts == map[] {
    assert forall x :: x in counts ==> counts[x] <= 0;
  } else {
    forall x | x in counts ensures counts[x] <= |a| {
      SetSizeEqualsCount(a, x);
    }
    
    assert exists maxCount :: maxCount >= 0 && forall x :: x in counts ==> counts[x] <= maxCount;
  }
}

lemma CountIncremental(a: seq<int>, i: int, val: int)
  requires 0 <= i < |a|
  ensures |set j | 0 <= j < i + 1 && a[j] == val| == |set j | 0 <= j < i && a[j] == val| + (if a[i] == val then 1 else 0)
{
  var s1 := set j | 0 <= j < i + 1 && a[j] == val;
  var s2 := set j | 0 <= j < i && a[j] == val;
  
  if a[i] == val {
    assert s1 == s2 + {i};
    assert i !in s2;
  } else {
    assert s1 == s2;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def histogram(s : str) -> Dict[str, int]
Given a string representing a space separated lowercase letters, return a dictionary of the letter with the most repetition and containing the corresponding count. If several letters have the same occurrence, return all of them.
*/
// </vc-description>

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
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in counts ==> counts[x] == |set j | 0 <= j < i && a[j] == x|
    invariant forall j :: 0 <= j < i ==> a[j] in counts
  {
    var current := a[i];
    CountIncremental(a, i, current);
    var currentCount := |set j | 0 <= j < i + 1 && a[j] == current|;
    counts := counts[current := currentCount];
    i := i + 1;
  }
  
  if |counts| == 0 {
    biggest := map[];
    return;
  }
  
  var maxCount := 0;
  var keys := counts.Keys;
  
  while keys != {}
    decreases |keys|
    invariant forall x :: x in counts.Keys - keys ==> x in counts && counts[x] <= maxCount
  {
    var key :| key in keys;
    assert key in counts;
    if counts[key] > maxCount {
      maxCount := counts[key];
    }
    keys := keys - {key};
  }
  
  biggest := map[];
  keys := counts.Keys;
  
  while keys != {}
    decreases |keys|
    invariant forall x :: x in counts.Keys - keys && counts[x] == maxCount ==> x in biggest && biggest[x] == maxCount
    invariant forall x :: x in biggest ==> x in counts && counts[x] == maxCount && biggest[x] == maxCount
  {
    var key :| key in keys;
    assert key in counts;
    if counts[key] == maxCount {
      biggest := biggest[key := maxCount];
    }
    keys := keys - {key};
  }
}
// </vc-code>


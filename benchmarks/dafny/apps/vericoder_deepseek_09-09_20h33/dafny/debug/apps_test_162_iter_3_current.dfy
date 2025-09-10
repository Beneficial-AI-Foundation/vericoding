predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && k >= 1 && |a| == n &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 1) &&
    (exists i :: 0 <= i < |a| && k % a[i] == 0)
}

predicate ValidBucket(k: int, bucketSize: int)
{
    bucketSize >= 1 && k % bucketSize == 0
}

function HoursNeeded(k: int, bucketSize: int): int
    requires ValidBucket(k, bucketSize)
{
    k / bucketSize
}

predicate IsOptimalChoice(k: int, a: seq<int>, chosenBucket: int)
{
    0 <= chosenBucket < |a| &&
    ValidBucket(k, a[chosenBucket]) &&
    (forall i :: 0 <= i < |a| && ValidBucket(k, a[i]) ==> a[i] <= a[chosenBucket])
}

// <vc-helpers>
lemma MaxBucketLemma(k: int, a: seq<int>)
  requires ValidInput(|a|, k, a)
  ensures exists i :: IsOptimalChoice(k, a, i)
{
  var maxValid := -1;
  var maxIndex := -1;
  
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant maxIndex == -1 ==> maxValid == -1
    invariant maxIndex >= 0 ==> 
      maxValid >= 1 && 
      ValidBucket(k, maxValid) && 
      maxIndex < |a| && 
      maxValid == a[maxIndex] &&
      (forall m :: 0 <= m < j && ValidBucket(k, a[m]) ==> a[m] <= maxValid)
  {
    if ValidBucket(k, a[j]) {
      if maxIndex == -1 || a[j] > maxValid {
        maxValid := a[j];
        maxIndex := j;
      } else {
        // Preserve invariant: a[j] <= maxValid in this case
      }
    }
    j := j + 1;
  }
  
  // Prove that at least one valid bucket exists
  assert exists i :: 0 <= i < |a| && ValidBucket(k, a[i]) by {
    var n' := |a|;
    assert ValidInput(n', k, a);
  };
  assert maxIndex >= 0 by {
    if maxIndex == -1 {
      assert !(exists i :: 0 <= i < |a| && ValidBucket(k, a[i]));
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
{
  var maxBucket := 0;
  var i := 0;
  var maxIndex := -1;
  
  while i < n
    invariant 0 <= i <= n
    invariant maxIndex == -1 ==> maxBucket == 0
    invariant maxIndex >= 0 ==> (maxIndex < i && ValidBucket(k, a[maxIndex]) && maxBucket == a[maxIndex])
    invariant maxBucket == 0 || ValidBucket(k, maxBucket)
    invariant maxBucket == 0 || 
      (forall m :: 0 <= m < i && ValidBucket(k, a[m]) ==> a[m] <= maxBucket)
  {
    if ValidBucket(k, a[i]) {
      if maxBucket == 0 || a[i] > maxBucket {
        maxBucket := a[i];
        maxIndex := i;
      }
    }
    i := i + 1;
  }
  
  assert maxBucket > 0 by {
    assert exists j :: 0 <= j < n && ValidBucket(k, a[j]) by {
      var exists_index := ValidInput(n, k, a);
    }
    if maxBucket == 0 {
      assert !(exists j :: 0 <= j < n && ValidBucket(k, a[j]));
      assert false;
    }
  }
  result := HoursNeeded(k, maxBucket);
}
// </vc-code>


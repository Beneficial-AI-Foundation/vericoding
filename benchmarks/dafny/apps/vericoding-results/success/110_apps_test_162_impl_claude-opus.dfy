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
lemma OptimalChoiceExists(n: int, k: int, a: seq<int>)
    requires ValidInput(n, k, a)
    ensures exists i :: IsOptimalChoice(k, a, i)
{
    // By ValidInput, we know there exists at least one valid bucket
    var validIdx :| 0 <= validIdx < |a| && k % a[validIdx] == 0;
    
    // Find the maximum valid bucket size
    var maxBucket := a[validIdx];
    var maxIdx := validIdx;
    
    var j := 0;
    while j < |a|
        invariant 0 <= j <= |a|
        invariant 0 <= maxIdx < |a|
        invariant ValidBucket(k, a[maxIdx])
        invariant forall i :: 0 <= i < j && ValidBucket(k, a[i]) ==> a[i] <= a[maxIdx]
    {
        if k % a[j] == 0 && a[j] > a[maxIdx] {
            maxIdx := j;
        }
        j := j + 1;
    }
    
    assert IsOptimalChoice(k, a, maxIdx);
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
    // Find the maximum valid bucket size
    var maxBucket := 0;
    var maxIdx := -1;
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant maxIdx >= -1 && maxIdx < |a|
        invariant maxIdx >= 0 ==> ValidBucket(k, a[maxIdx])
        invariant maxIdx >= 0 ==> maxBucket == a[maxIdx]
        invariant forall j :: 0 <= j < i && ValidBucket(k, a[j]) ==> 
                    (maxIdx >= 0 && a[j] <= a[maxIdx])
    {
        if k % a[i] == 0 {
            if maxIdx == -1 || a[i] > maxBucket {
                maxBucket := a[i];
                maxIdx := i;
            }
        }
        i := i + 1;
    }
    
    // By ValidInput, we must have found at least one valid bucket
    assert maxIdx >= 0;
    assert IsOptimalChoice(k, a, maxIdx);
    
    result := k / a[maxIdx];
}
// </vc-code>


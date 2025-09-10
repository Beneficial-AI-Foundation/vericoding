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
// No additional helpers needed.
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
{
    var chosenIndex: int := -1;
    var i: int := 0;
    while i < n
        invariant 0 <= i <= n
        invariant chosenIndex == -1 ==> forall j :: 0 <= j < i ==> !ValidBucket(k, a[j])
        invariant chosenIndex >= 0 ==> (chosenIndex < i && ValidBucket(k, a[chosenIndex]) && 
                                        forall j :: 0 <= j < i ==> ValidBucket(k, a[j]) ==> a[j] <= a[chosenIndex])
    {
        if k % a[i] == 0 {
            if chosenIndex == -1 || a[i] > a[chosenIndex] {
                chosenIndex := i;
            }
        }
        i := i + 1;
    }
    result := k / a[chosenIndex];
}
// </vc-code>


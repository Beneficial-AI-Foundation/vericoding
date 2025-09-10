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
lemma ValidBucketExists(k: int, a: seq<int>)
    requires |a| >= 1
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    requires exists i :: 0 <= i < |a| && k % a[i] == 0
    ensures exists i :: 0 <= i < |a| && ValidBucket(k, a[i])
{
}

lemma OptimalChoiceExists(k: int, a: seq<int>)
    requires |a| >= 1
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    requires exists i :: 0 <= i < |a| && k % a[i] == 0
    ensures exists i :: IsOptimalChoice(k, a, i)
{
    ValidBucketExists(k, a);
    var validIndices := set i | 0 <= i < |a| && ValidBucket(k, a[i]);
    assert validIndices != {};
    
    var maxBucket := MaxInSet(validIndices, a);
    assert maxBucket in validIndices;
    assert IsOptimalChoice(k, a, maxBucket);
}

function MaxInSet(indices: set<int>, a: seq<int>): int
    requires indices != {}
    requires forall i :: i in indices ==> 0 <= i < |a|
    ensures MaxInSet(indices, a) in indices
    ensures forall i :: i in indices ==> a[i] <= a[MaxInSet(indices, a)]
{
    if |indices| == 1 then
        var x :| x in indices; x
    else
        var x :| x in indices;
        var rest := indices - {x};
        var maxRest := MaxInSet(rest, a);
        if a[x] >= a[maxRest] then x else maxRest
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
    OptimalChoiceExists(k, a);
    var validIndices := set i | 0 <= i < |a| && ValidBucket(k, a[i]);
    var optimalIndex := MaxInSet(validIndices, a);
    result := HoursNeeded(k, a[optimalIndex]);
}
// </vc-code>


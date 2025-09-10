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
lemma DivisibilityImpliesNonZero(k: int, d: int)
    requires k % d == 0
    ensures d != 0
{
    if d == 0 {
        calc {
            k % 0;
            { assert false; }
            k % 0;
        }
    }
}

lemma DivisorsAreAtLeastOne(k: int, d: int)
    requires k % d == 0
    ensures d >= 1
{
    DivisibilityImpliesNonZero(k, d);
    if d < 0 {
        calc {
            k % d;
            k % (-d);
            { assert k % (-d) == -(k % d); }
            -(k % d);
        }
    }
    assert d > 0 || d < 0;
    if d < 0 {
        assert -d > 0;
    }
}

lemma OptimalChoiceIsDivisor(n: int, k: int, a: seq<int>, chosenBucket: int)
    requires 0 <= chosenBucket < |a|
    requires ValidInput(n, k, a)
    requires IsOptimalChoice(k, a, chosenBucket)
    ensures k % a[chosenBucket] == 0
{
    if k % a[chosenBucket] != 0 {
        calc {
            k % a[chosenBucket] != 0;
            !ValidBucket(k, a[chosenBucket]);
            false;
        }
    }
}

lemma OptimalChoiceImpliesValidBucket(n: int, k: int, a: seq<int>, chosenBucket: int)
    requires 0 <= chosenBucket < |a|
    requires ValidInput(n, k, a)
    requires IsOptimalChoice(k, a, chosenBucket)
    ensures ValidBucket(k, a[chosenBucket])
{
    DivisorsAreAtLeastOne(k, a[chosenBucket]);
    assert a[chosenBucket] >= 1;
    assert k % a[chosenBucket] == 0;
}

lemma OptimalChoiceImpliesHoursNeeded(n: int, k: int, a: seq<int>, chosenBucket: int)
    requires 0 <= chosenBucket < |a|
    requires ValidInput(n, k, a)
    requires IsOptimalChoice(k, a, chosenBucket)
    ensures HoursNeeded(k, a[chosenBucket]) >= 1
{
    OptimalChoiceImpliesValidBucket(n, k, a, chosenBucket);
    calc {
        HoursNeeded(k, a[chosenBucket]);
        k / a[chosenBucket];
    }
    assert a[chosenBucket] <= k by { assert k / a[chosenBucket] >= 1; }
}

lemma OptimalChoiceFromMaxDivisor(n: int, k: int, a: seq<int>, idx: int, max_divisor: int)
    requires 0 <= idx < |a|
    requires ValidInput(n, k, a)
    requires a[idx] == max_divisor
    requires k % max_divisor == 0
    requires forall j :: 0 <= j < |a| && k % a[j] == 0 ==> a[j] <= max_divisor
    ensures IsOptimalChoice(k, a, idx)
{
    DivisorsAreAtLeastOne(k, max_divisor);
    assert a[idx] >= 1;
    assert k % a[idx] == 0;
    forall i | 0 <= i < |a| && ValidBucket(k, a[i])
        ensures a[i] <= a[idx]
    {
        assert k % a[i] == 0;
        assert a[i] <= max_divisor;
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
    var max_divisor := 0;
    var max_index := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant max_divisor >= 0
        invariant max_index >= 0
        invariant max_index < i ==> (max_divisor > 0 && k % a[max_index] == 0 && a[max_index] == max_divisor)
        invariant forall j :: 0 <= j < i && k % a[j] == 0 ==> a[j] <= max_divisor
    {
        if k % a[i] == 0 {
            if a[i] > max_divisor {
                max_divisor := a[i];
                max_index := i;
            }
        }
        i := i + 1;
    }
    
    assert max_divisor > 0;
    assert max_index < n;
    assert k % a[max_index] == 0;
    assert a[max_index] == max_divisor;
    assert forall j :: 0 <= j < n && k % a[j] == 0 ==> a[j] <= max_divisor;
    
    OptimalChoiceFromMaxDivisor(n, k, a, max_index, max_divisor);
    
    result := k / a[max_index];
}
// </vc-code>


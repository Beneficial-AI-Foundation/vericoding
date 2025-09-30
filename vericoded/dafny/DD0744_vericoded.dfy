

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
// </vc-spec>
// <vc-code>
{
    sorted := true;
    var k := 0;
    
    while k < a.Length - 1
        invariant 0 <= k <= a.Length - 1
        invariant sorted ==> forall i, j :: 0 <= i < j <= k ==> a[i] <= a[j]
        invariant !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
    {
        if a[k] > a[k + 1] {
            sorted := false;
            assert a[k] > a[k + 1];
            assert 0 <= k < k + 1 < a.Length;
            return;
        }
        k := k + 1;
    }
}
// </vc-code>


// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsSortedImpl(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
{
    sorted := true;
    for i := 0 to a.Length - 1
        invariant 0 <= i <= a.Length - 1
        invariant sorted ==> forall k, l :: 0 <= k < l <= i ==> a[k] <= a[l]
        invariant !sorted ==> exists k, l :: 0 <= k < l <= i && a[k] > a[l]
    {
        for j := i + 1 to a.Length
            invariant i + 1 <= j <= a.Length
            invariant sorted ==> forall k :: i + 1 <= k < j ==> a[i] <= a[k]
            invariant !sorted ==> exists k, l :: 0 <= k < l <= i && a[k] > a[l]
        {
            if a[i] > a[j] {
                sorted := false;
                return;
            }
        }
    }
}
// </vc-code>

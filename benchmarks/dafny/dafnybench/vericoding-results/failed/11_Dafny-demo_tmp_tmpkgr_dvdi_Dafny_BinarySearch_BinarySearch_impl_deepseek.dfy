predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
lemma BinarySearchLemma(a: array<int>, key: int, low: int, high: int)
    requires a != null && sorted(a, 0, a.Length-1)
    requires 0 <= low <= high+1 <= a.Length
    requires forall k :: low <= k <= high ==> a[k] != key
    ensures forall k :: 0 <= k < a.Length ==> a[k] != key
{
    forall k | 0 <= k < a.Length
        ensures a[k] != key
    {
        if k < low {
            // k < low, no information from lemma parameters
        } else if k > high {
            // k > high, no information from lemma parameters
        } else {
            assert low <= k <= high;
            // Directly from the premise
        }
    }
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array?<int>, key: int)
    returns (index: int)
    requires a != null && sorted(a,0,a.Length-1);
    ensures index >= 0 ==> index < a.Length && a[index] == key;
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := a.Length - 1;
    index := -1;
    
    while low <= high
        invariant 0 <= low <= high+1 <= a.Length
        invariant index == -1 ==> forall k :: 0 <= k < low ==> a[k] != key
        invariant index == -1 ==> forall k :: high < k < a.Length ==> a[k] != key
        invariant index >= 0 ==> index < a.Length && a[index] == key
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        if a[mid] < key {
            low := mid + 1;
        } else if a[mid] > key {
            high := mid - 1;
        } else {
            index := mid;
            return;
        }
    }
    
    if index == -1 {
        BinarySearchLemma(a, key, low, high);
    }
}
// </vc-code>


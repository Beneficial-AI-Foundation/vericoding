predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
lemma SortedSlice(a: array<int>, l: int, u: int, l': int, u': int)
    requires 0 <= l <= u < a.Length
    requires sorted(a, l, u)
    requires l <= l' <= u' <= u
    ensures sorted(a, l', u')
{
    if l' <= u' {
        forall i, j | l' <= i <= j <= u'
            ensures a[i] <= a[j]
        {
            assert l <= i <= j <= u;
            assert a[i] <= a[j];
        }
    }
}

lemma SortedImpliesOrdered(a: array<int>, i: int, j: int)
    requires sorted(a, 0, a.Length - 1)
    requires 0 <= i <= j < a.Length
    ensures a[i] <= a[j]
{
    assert forall x, y :: 0 <= 0 <= x <= y <= a.Length - 1 < a.Length ==> a[x] <= a[y];
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BinarySearch(a: array?<int>, key: int)
    returns (index: int)
    requires a != null && sorted(a,0,a.Length-1);
    ensures index >= 0 ==> index < a.Length && a[index] == key;
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length == 0 {
        return -1;
    }
    
    var low := 0;
    var high := a.Length - 1;
    
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant high < low ==> forall k :: 0 <= k < a.Length ==> a[k] != key
        invariant low > 0 ==> forall k :: 0 <= k < low ==> a[k] < key
        invariant high < a.Length - 1 ==> forall k :: high < k < a.Length ==> a[k] > key
        invariant sorted(a, 0, a.Length - 1)
    {
        var mid := (low + high) / 2;
        
        if a[mid] == key {
            return mid;
        } else if a[mid] < key {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    return -1;
}
// </vc-code>

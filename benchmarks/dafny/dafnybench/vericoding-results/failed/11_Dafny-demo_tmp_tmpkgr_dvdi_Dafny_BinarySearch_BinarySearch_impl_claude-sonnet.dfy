predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
lemma SortedProperty(a: array<int>, l: int, u: int, i: int, j: int)
    requires sorted(a, l, u)
    requires 0 <= l <= i <= j <= u < a.Length
    ensures a[i] <= a[j]
{
    // This lemma is automatically proven by the definition of sorted
}

lemma SortedSubrange(a: array<int>, l: int, u: int, l': int, u': int)
    requires sorted(a, l, u)
    requires 0 <= l <= l' <= u' <= u < a.Length
    ensures sorted(a, l', u')
{
    // This lemma is automatically proven by the definition of sorted
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
    if a.Length == 0 {
        return -1;
    }
    
    var low := 0;
    var high := a.Length - 1;
    
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant forall i :: 0 <= i < low ==> a[i] < key
        invariant forall i :: high < i < a.Length ==> a[i] > key
        decreases high - low
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


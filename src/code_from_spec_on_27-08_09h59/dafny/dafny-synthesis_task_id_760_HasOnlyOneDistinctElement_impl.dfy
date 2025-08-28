// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length == 0 {
        return true;
    }
    
    var firstElement := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] == firstElement
    {
        if a[i] != firstElement {
            return false;
        }
        i := i + 1;
    }
    
    return true;
}
// </vc-code>

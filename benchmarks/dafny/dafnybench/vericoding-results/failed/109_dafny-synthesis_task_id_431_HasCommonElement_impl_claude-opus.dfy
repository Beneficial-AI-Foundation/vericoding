

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
    result := false;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !result ==> forall i', j' :: 0 <= i' < i && 0 <= j' < b.Length ==> a[i'] != b[j']
        invariant result ==> exists i', j' :: 0 <= i' < a.Length && 0 <= j' < b.Length && a[i'] == b[j']
    {
        var j := 0;
        
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant !result ==> forall i', j' :: 0 <= i' < i && 0 <= j' < b.Length ==> a[i'] != b[j']
            invariant !result ==> forall j' :: 0 <= j' < j ==> a[i] != b[j']
            invariant result ==> exists i', j' :: 0 <= i' < a.Length && 0 <= j' < b.Length && a[i'] == b[j']
        {
            if a[i] == b[j] {
                result := true;
                return;
            }
            j := j + 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>


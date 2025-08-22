//IMPL 
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
{
    if a.Length == 0 {
        result := true;
        return;
    }
    
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] == a[0]
    {
        if a[i] != a[0] {
            result := false;
            return;
        }
        i := i + 1;
    }
    
    result := true;
}
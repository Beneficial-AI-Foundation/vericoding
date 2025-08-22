//IMPL 
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
{
    result := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !result ==> forall x, y :: 0 <= x < i && 0 <= y < b.Length ==> a[x] != b[y]
        invariant result ==> exists x, y :: 0 <= x < a.Length && 0 <= y < b.Length && a[x] == b[y]
    {
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant !result ==> forall y :: 0 <= y < j ==> a[i] != b[y]
            invariant !result ==> forall x, y :: 0 <= x < i && 0 <= y < b.Length ==> a[x] != b[y]
            invariant result ==> exists x, y :: 0 <= x < a.Length && 0 <= y < b.Length && a[x] == b[y]
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
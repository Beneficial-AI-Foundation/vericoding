// IMPL
method minArray(a: array<int>) returns (r:int)
 requires a.Length > 0
 ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
 ensures exists i :: 0 <= i < a.Length && r == a[i]
{
    r := a[0];
    var j := 1;
    while j < a.Length
        invariant 1 <= j <= a.Length
        invariant forall k :: 0 <= k < j ==> r <= a[k]
        invariant exists k :: 0 <= k < j && r == a[k]
    {
        if a[j] < r {
            r := a[j];
        }
        j := j + 1;
    }
}
//IMPL
method Busca<T(==)>(a:array<T>, x:T) returns (r:int)
 ensures 0 <= r ==> r < a.Length && a[r] == x
 ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != x
    {
        if a[i] == x {
            r := i;
            return;
        }
        i := i + 1;
    }
    r := -1;
}
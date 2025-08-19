//IMPL 

method buscar(a:array<int>, x:int) returns (r:int)
ensures r < 0 ==> forall i :: 0 <= i <a.Length ==> a[i] != x
ensures 0 <= r < a.Length ==> a[r] == x
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != x
    {
        if a[i] == x {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
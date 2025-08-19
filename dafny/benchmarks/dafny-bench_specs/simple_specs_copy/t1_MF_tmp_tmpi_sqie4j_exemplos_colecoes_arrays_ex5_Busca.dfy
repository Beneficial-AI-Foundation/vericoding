// SPEC
method Busca<T(==)>(a:array<T>, x:T) returns (r:int)
 ensures 0 <= r ==> r < a.Length && a[r] == x
 ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
}

//IMPL 
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall j :: 0 <= j < i ==> a[j] == n
        invariant !result ==> exists j :: 0 <= j < i && a[j] != n
    {
        if a[i] != n {
            result := false;
            return;
        }
        i := i + 1;
    }
}
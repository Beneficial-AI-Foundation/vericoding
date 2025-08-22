//IMPL 
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{
    for i := 0 to a.Length
        invariant forall j :: 0 <= j < i ==> n > a[j]
    {
        if n <= a[i] {
            result := false;
            return;
        }
    }
    result := true;
}
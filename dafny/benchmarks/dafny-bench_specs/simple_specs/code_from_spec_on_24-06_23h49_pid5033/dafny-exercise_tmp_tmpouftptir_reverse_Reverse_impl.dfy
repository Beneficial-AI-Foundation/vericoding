//IMPL 
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a == old(a)
ensures b.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
{
    b := new char[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant b.Length == a.Length
        invariant forall j :: 0 <= j < i ==> b[j] == a[a.Length - j - 1]
    {
        b[i] := a[a.Length - i - 1];
        i := i + 1;
    }
}
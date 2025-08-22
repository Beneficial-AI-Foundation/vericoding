//IMPL 
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k]
{
    b := new char[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant b.Length == a.Length
        invariant forall k :: 0 <= k < i ==> b[k] == a[(a.Length-1) - k]
    {
        b[i] := a[(a.Length-1) - i];
        i := i + 1;
    }
}
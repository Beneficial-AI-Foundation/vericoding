// ATOM 
datatype Color = Red | White | Blue
// ATOM 

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}




// SPEC 



method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
{
}



// ATOM 
datatype Color = Red | White | Blue
// ATOM 

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}

//IMPL DutchFlag
method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    if a.Length <= 1 {
        return;
    }
    
    var red := 0;
    var white := 0; 
    var blue := a.Length;
    
    while white < blue
        invariant 0 <= red <= white <= blue <= a.Length
        invariant forall k :: 0 <= k < red ==> a[k] == Red
        invariant forall k :: red <= k < white ==> a[k] == White
        invariant forall k :: blue <= k < a.Length ==> a[k] == Blue
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[white] == White {
            white := white + 1;
        } else if a[white] == Red {
            a[white], a[red] := a[red], a[white];
            red := red + 1;
            white := white + 1;
        } else {
            blue := blue - 1;
            a[white], a[blue] := a[blue], a[white];
        }
    }
}
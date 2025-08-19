//ATOM
datatype Color = Red | White | Blue


//ATOM

predicate Below(c: Color, d: Color)
{
  c == Red || c == d || d == Blue
}


//IMPL 

method DutchFlag(a: array<Color>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if a.Length <= 1 { return; }
  
  var red := 0;
  var white := 0;
  var blue := a.Length;
  
  while white < blue
    invariant 0 <= red <= white <= blue <= a.Length
    invariant forall i :: 0 <= i < red ==> a[i] == Red
    invariant forall i :: red <= i < white ==> a[i] == White
    invariant forall i :: blue <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[white] == Red {
      a[red], a[white] := a[white], a[red];
      red := red + 1;
      white := white + 1;
    } else if a[white] == White {
      white := white + 1;
    } else {
      blue := blue - 1;
      a[white], a[blue] := a[blue], a[white];
    }
  }
}
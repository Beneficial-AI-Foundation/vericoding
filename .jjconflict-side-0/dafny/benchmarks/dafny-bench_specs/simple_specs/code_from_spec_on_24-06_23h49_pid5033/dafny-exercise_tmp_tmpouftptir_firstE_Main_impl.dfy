//ATOM
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
{
  x := 0;
  while x < a.Length
    invariant 0 <= x <= a.Length
    invariant forall i | 0 <= i < x :: a[i] != 'e'
  {
    if a[x] == 'e' {
      return;
    }
    x := x + 1;
  }
  x := -1;
}

//IMPL Main
method Main() {
  var a: array<char> := new char[6] ['c','h','e','e','s','e'];
  var res := firstE(a);
  
  a := new char[1] ['e'];
  res := firstE(a);
  
  a := new char[0];
  res := firstE(a);
}
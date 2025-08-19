//ATOM

method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
{
  b := [];
  assume a.Length ==> b.Length;
  assume forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1];
  return b;
}


// SPEC

method Main()
{
 var a := new char[8];
 a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 'd', 'e', 's', 'r', 'e', 'v', 'e', 'r';
 var b := Reverse(a);
 print b[..];

 a := new char[1];
 a[0] := '!';
 b := Reverse(a);
 print b[..], '\n';
}
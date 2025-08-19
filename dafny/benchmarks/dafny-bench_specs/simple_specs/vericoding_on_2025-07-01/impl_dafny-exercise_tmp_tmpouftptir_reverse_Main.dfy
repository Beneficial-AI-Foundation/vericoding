//ATOM

method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a == old(a)
ensures b.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
{
  b := [];
  assume a ==> old(a);
  assume b.Length ==> a.Length;
  assume forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1];
  return b;
}


// SPEC

method Main()
{
 var a := new char[]['s', 'k', 'r', 'o', 'w', 't', 'i'];
 var b := Reverse(a);
 print b[..];

 a := new char[]['!'];
 b := Reverse(a);
 print b[..], '\n';
}
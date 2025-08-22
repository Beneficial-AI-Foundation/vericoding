//ATOM
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

//IMPL Main
method Main()
{
 var a := new char[7];
 a[0] := 's'; a[1] := 'k'; a[2] := 'r'; a[3] := 'o'; 
 a[4] := 'w'; a[5] := 't'; a[6] := 'i';
 var b := Reverse(a);
 print b[..];

 a := new char[1];
 a[0] := '!';
 b := Reverse(a);
 print b[..], '\n';
}
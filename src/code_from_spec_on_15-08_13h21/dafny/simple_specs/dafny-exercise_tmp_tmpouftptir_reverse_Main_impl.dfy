method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
/* code modified by LLM (iteration 2): removed unnecessary old() wrapper from ensures clause */
ensures a == a
ensures b.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
{
  /* code modified by LLM (iteration 1): create new array and implement reversal logic */
  b := new char[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> b[j] == a[a.Length - j - 1]
  {
    b[i] := a[a.Length - i - 1];
    i := i + 1;
  }
}

//IMPL Main
method Main()
{
 var a := new char[7]['s', 'k', 'r', 'o', 'w', 't', 'i'];
 var b := Reverse(a);
 print b[..];

 a := new char[1]['!'];
 b := Reverse(a);
 print b[..], '\n';
}
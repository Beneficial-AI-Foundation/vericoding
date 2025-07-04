//ATOM
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
{
  /* code modified by LLM (iteration 1): fixed array initialization syntax and provided proper implementation */
  b := new char[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == a[a.Length - k - 1]
  {
    b[i] := a[a.Length - i - 1];
    i := i + 1;
  }
}

//IMPL Main
method Main()
{
  /* code modified by LLM (iteration 1): preserved original implementation */
  var a := new char[8];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 'd', 'e', 's', 'r', 'e', 'v', 'e', 'r';
  var b := Reverse(a);
  print b[..];

  a := new char[1];
  a[0] := '!';
  b := Reverse(a);
  print b[..], '\n';
}
function abs(a:int):nat
{
    if a < 0 then -a else a
}

// <vc-helpers>
// </vc-helpers>

method aba(a:array<int>)returns (b:array<int>)
ensures a.Length == b.Length // needed for next line
ensures forall x :: 0<=x<b.Length ==> b[x] == abs(a[x])
// </vc-spec>
// <vc-code>
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> b[x] == abs(a[x])
  {
    b[i] := abs(a[i]);
    i := i + 1;
  }
}
// </vc-code>
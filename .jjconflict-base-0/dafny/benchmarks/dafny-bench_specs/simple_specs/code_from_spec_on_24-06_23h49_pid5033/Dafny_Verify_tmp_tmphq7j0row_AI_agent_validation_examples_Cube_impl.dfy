//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  m := 0;
  assume forall i :: 0 <= i < a.Length ==> a[i] <= m;
  assume (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i];
  return m;
}

//IMPL Cube
method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}
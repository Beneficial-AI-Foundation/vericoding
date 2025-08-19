//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  /* code modified by LLM (iteration 1): Fixed compilation errors - replaced ==> with == in logical expressions and removed assume statements */
  if a.Length == 0 {
    m := 0;
    return;
  }
  
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && m == a[j]
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}

//IMPL Cube
method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  /* code modified by LLM (iteration 1): Added implementation for Cube method */
  c := n * n * n;
}
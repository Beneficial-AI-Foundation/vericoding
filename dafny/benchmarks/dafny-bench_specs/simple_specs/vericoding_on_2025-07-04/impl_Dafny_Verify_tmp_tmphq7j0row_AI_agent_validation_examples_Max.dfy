//ATOM

function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL ComputePower1
method ComputePower1(N: int) returns (y: nat) 
  requires N >= 0
  ensures y == Power(N)
{
  /* code modified by LLM (iteration 1): Added complete implementation using iterative approach */
  if N == 0 {
    y := 1;
  } else {
    y := 1;
    var i := 0;
    while i < N
      invariant 0 <= i <= N
      invariant y == Power(i)
    {
      y := y * 2;
      i := i + 1;
    }
  }
}

//IMPL Max
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  /* code modified by LLM (iteration 1): Added complete implementation handling empty and non-empty arrays */
  if a.Length == 0 {
    m := 0;
  } else {
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
}
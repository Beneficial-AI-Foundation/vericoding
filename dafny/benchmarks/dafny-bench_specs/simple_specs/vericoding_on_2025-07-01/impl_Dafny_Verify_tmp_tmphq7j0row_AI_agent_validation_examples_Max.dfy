//ATOM

function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}


// SPEC


// Original davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//   ensures y == Power(N)
// {
}



// Fine_tuned davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//   ensures y == Power(N)
// {
}

method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
}
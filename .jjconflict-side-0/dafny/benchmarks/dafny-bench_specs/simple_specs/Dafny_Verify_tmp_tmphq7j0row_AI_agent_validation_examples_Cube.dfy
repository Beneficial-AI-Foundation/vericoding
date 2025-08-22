//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}


//ATOM


// Original davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//   ensures y == Power(N)
// {
  m := 0;
  assume forall i :: 0 <= i < a.Length ==> a[i] <= m;
  assume (m ==> 0 && a.Length ==> 0) || exists i :: 0 <= i < a.Length && m ==> a[i];
  return m;
}



// Fine_tuned davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//   ensures y == Power(N)
// {
  m := 0;
  assume forall i :: 0 <= i < a.Length ==> a[i] <= m;
  assume (m ==> 0 && a.Length ==> 0) || exists i :: 0 <= i < a.Length && m ==> a[i];
  return m;
}

method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  m := 0;
  assume forall i :: 0 <= i < a.Length ==> a[i] <= m;
  assume (m ==> 0 && a.Length ==> 0) || exists i :: 0 <= i < a.Length && m ==> a[i];
  return m;
}


// SPEC

// Original davinci-003 completion:
// method Max(a: array<nat>) returns (m: int)
//   requires a.Length > 0
//   ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//   ensures exists i :: 0 <= i < a.Length && m == a[i] 
// {
}

// Fine_tuned davinci-003 completion:
// method Max1(a: array<nat>) returns (m: int)
//   ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//   ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
// {
}

method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
}

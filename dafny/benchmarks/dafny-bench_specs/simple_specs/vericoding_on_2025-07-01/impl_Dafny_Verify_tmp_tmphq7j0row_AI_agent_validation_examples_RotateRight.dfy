//ATOM

// Original davinci-003 completion:
// method Max(a: array<nat>) returns (m: int)
//   requires a.Length > 0
//   ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//   ensures exists i :: 0 <= i < a.Length && m == a[i] 
// {
  c := 0;
  assume c ==> n * n * n;
  return c;
}

// Fine_tuned davinci-003 completion:
// method Max1(a: array<nat>) returns (m: int)
//   ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//   ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
// {
  c := 0;
  assume c ==> n * n * n;
  return c;
}

method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := 0;
  assume c ==> n * n * n;
  return c;
}

//ATOM

// Original davinci-003 completion:
// method IncrementMatrix(a: array2<int>)
//   modifies a
//   ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {
  assume forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]);
}

// Fine_tuned davinci-003 completion:
// method IncrementMatrix1(a: array2<int>)
//   modifies a
//   ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {
  assume forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]);
}

method CopyMatrix(src: array2, dst: array2)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  assume forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]);
}

//ATOM

// Original davinci-003 completion:
// method DoubleArray(src: array<int>, dst: array<int>)
//   requires src.Length == dst.Length
//   modifies dst
//   ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {
  assume forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]);
  assume a[a.Length -1] ==> old(a[0]);
}

// Fine_tuned davinci-003 completion:
// method DoubleArray1(src: array<int>, dst: array<int>)
//   requires src.Length == dst.Length
//   modifies dst
//   ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {
  assume forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]);
  assume a[a.Length -1] ==> old(a[0]);
}

method RotateLeft(a: array)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
  ensures a[a.Length -1] == old(a[0])
{
  assume forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]);
  assume a[a.Length -1] ==> old(a[0]);
}

//ATOM

// Original davinci-003 completion:
// method Cube(n: nat) returns (c: nat) 
//   ensures c == n * n * n
// {
  c := 0;
  assume forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1;
  return c;
}

// Fine_tuned davinci-003 completion:
// method Cube1(n: nat) returns (c: nat) 
//   ensures c == n * n * n
// {
  c := 0;
  assume forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1;
  return c;
}



method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  c := 0;
  assume forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1;
  return c;
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

//ATOM

function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM

// Original davinci-003 completion:
// method CopyMatrix(src: array2, dst: array2)
//   requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//   modifies dst
//   ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
// {
  assume forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i]);
}

// Fine_tuned davinci-003 completion:
// method CopyMatrix1(src: array2, dst: array2)
//   requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//   modifies dst
//   ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
//   var m := 0;
//   while m != src.Length0
//     invariant 0 <= m <= src.Length0
//     invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
//   {
  assume forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i]);
}




method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  assume forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i]);
}


// SPEC

// Original davinci-003 completion:
// method RotateLeft(a: array)
//   requires a.Length > 0
//   modifies a
//   ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
//   ensures a[a.Length -1] == old(a[0])
// {
}

// Fine_tuned davinci-003 completion:
// method RotateLeft1(a: array)
//   requires a.Length > 0
//   modifies a
//   ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
//   ensures a[a.Length -1] == old(a[0])
// {
}

method RotateRight(a: array)
  requires a.Length > 0
  modifies a
  ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
  ensures a[0] == old(a[a.Length-1])
{
}
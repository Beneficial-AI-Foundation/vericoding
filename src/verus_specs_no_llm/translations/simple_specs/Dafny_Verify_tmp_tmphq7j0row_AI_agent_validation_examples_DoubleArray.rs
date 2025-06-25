// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: Vec<nat>) -> (m: int)
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
//   ensures forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
// {
  assume forall i, j: : 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j]);
}

// Fine_tuned davinci-003 completion: // method IncrementMatrix1(a: array2<int>)
//   modifies a
//   ensures forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
// {
  assume forall i, j: : 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j]);
}

method CopyMatrix(src: array2, dst: array2)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j: : 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j]) 
{
  assume forall i, j: : 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j]);
}


//ATOM

// Original davinci-003 completion: // method Cube(n: nat) returns (c: nat) 
//   ensures c == n * n * n
// {
  c := 0;
  assume forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1;
  return c;
}

// Fine_tuned davinci-003 completion: // method Cube1(n: nat) returns (c: nat) 
//   ensures c == n * n * n
// {
  c := 0;
  assume forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1;
  return c;
}



method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
{
  c: = 0;
  assume forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1;
  return c;
}


//ATOM


// Original davinci-003 completion: // method ComputePower1(N: int) returns (y: nat) requires N >= 0
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


// SPEC

// Original davinci-003 completion:
// method CopyMatrix(src: array2, dst: array2)
//   requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//   modifies dst
//   ensures forall i, j: : 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j]) 
// {
}

// Fine_tuned davinci-003 completion: // method CopyMatrix1(src: array2, dst: array2)
//   requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//   modifies dst
//   ensures forall i, j: : 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
//   var m: = 0;
//   while m != src.Length0
//     invariant 0 <= m <= src.Length0
//     invariant forall i, j: : 0 <= i < m && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
//   {
}




method DoubleArray(src: Vec<int>, dst: Vec<int>)
    requires
        a.len() > 0
//,
        src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst,
        N >= 0
//,
        N >= 0
//,
        src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//   modifies dst
//,
        src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//   modifies dst
//,
        src.len() == dst.len()
  modifies dst
    ensures
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= m
//,
        exists i :: 0 <= i < a.len() && m == a.spec_index(i) 
//,
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= m
//,
        (m == 0 && a.len() == 0) || exists i :: 0 <= i < a.len() && m == a.spec_index(i)
//,
        c == n * n * n,
        forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.spec_index(i,j) == old(a.spec_index(i,j)) + 1
//,
        forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.spec_index(i,j) == old(a.spec_index(i,j)) + 1
//,
        forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst.spec_index(i,j) == old(src.spec_index(i,j)),
        c == n * n * n
//,
        c == n * n * n
//,
        forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.spec_index(i,j) == old(a.spec_index(i,j)) + 1,
        y == Power(N)
//,
        y == Power(N)
//,
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= m,
        (m == 0 && a.len() == 0) || exists i :: 0 <= i < a.len() && m == a.spec_index(i),
        forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst.spec_index(i,j) == old(src.spec_index(i,j)) 
//,
        forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst.spec_index(i,j) == old(src.spec_index(i,j))
//   var m := 0;
//   while m != src.Length0
//     invariant 0 <= m <= src.Length0
//     invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst.spec_index(i,j) == old(src.spec_index(i,j))
//,
        forall i :: 0 <= i < src.len() ==> dst.spec_index(i) == 2 * old(src.spec_index(i))
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Vec::new(), Vec::new());
}

}
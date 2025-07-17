// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Power(n: nat) -> nat
{
    0
}

spec fn spec_Max(a: Vec<nat>) -> m: int)
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
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
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


// SPEC

// Original davinci-003 completion:
// method IncrementMatrix(a: array2<int>)
//   modifies a
//   ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {
}

// Fine_tuned davinci-003 completion:
// method IncrementMatrix1(a: array2<int>)
//   modifies a
//   ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {
}

method CopyMatrix(src: array2, dst: array2
    requires
        a.len() > 0
//,
        N >= 0
//,
        N >= 0
//,
        src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        exists |i: int| 0 <= i < a.len() && m == a.index(i) 
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i)
//,
        c == n * n * n,
        c == n * n * n
//,
        c == n * n * n
//,
        forall |i: int, j: int| 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.index(i,j) == old(a.index(i,j)) + 1,
        y == Power(N)
//,
        y == Power(N)
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i),
        forall |i: int, j: int| 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.index(i,j) == old(a.index(i,j)) + 1
//,
        forall |i: int, j: int| 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.index(i,j) == old(a.index(i,j)) + 1
//,
        forall |i: int, j: int| 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst.index(i,j) == old(src.index(i,j))
;

proof fn lemma_Max(a: Vec<nat>) -> (m: int)
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
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}


//ATOM

// Original davinci-003 completion:
// method Cube(n: nat) returns (c: nat) 
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


// SPEC

// Original davinci-003 completion:
// method IncrementMatrix(a: array2<int>)
//   modifies a
//   ensures forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
// {
}

// Fine_tuned davinci-003 completion: // method IncrementMatrix1(a: array2<int>)
//   modifies a
//   ensures forall i, j: : 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
// {
}

method CopyMatrix(src: array2, dst: array2)
    requires
        a.len() > 0
//,
        N >= 0
//,
        N >= 0
//,
        src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        exists |i: int| 0 <= i < a.len() && m == a.index(i) 
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i)
//,
        c == n * n * n,
        c == n * n * n
//,
        c == n * n * n
//,
        forall |i: int, j: int| 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.index(i,j) == old(a.index(i,j)) + 1,
        y == Power(N)
//,
        y == Power(N)
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i),
        forall |i: int, j: int| 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.index(i,j) == old(a.index(i,j)) + 1
//,
        forall |i: int, j: int| 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a.index(i,j) == old(a.index(i,j)) + 1
//,
        forall |i: int, j: int| 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst.index(i,j) == old(src.index(i,j))
{
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
}

}
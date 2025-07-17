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

spec fn spec_ComputePower1(N: int) -> y: nat) requires N >= 0
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

method Cube(n: nat) returns (c: nat
    requires
        N >= 0
//,
        N >= 0
//,
        a.len() > 0
//
    ensures
        y == Power(N)
//,
        y == Power(N)
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i),
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        exists |i: int| 0 <= i < a.len() && m == a.index(i) 
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i)
//,
        c == n * n * n
;

proof fn lemma_ComputePower1(N: int) -> (y: nat) requires N >= 0
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
    requires
        N >= 0
//,
        N >= 0
//,
        a.len() > 0
//
    ensures
        y == Power(N)
//,
        y == Power(N)
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i),
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        exists |i: int| 0 <= i < a.len() && m == a.index(i) 
//,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m
//,
        (m == 0 && a.len() == 0) || exists |i: int| 0 <= i < a.len() && m == a.index(i)
//,
        c == n * n * n
{
    0
}

}
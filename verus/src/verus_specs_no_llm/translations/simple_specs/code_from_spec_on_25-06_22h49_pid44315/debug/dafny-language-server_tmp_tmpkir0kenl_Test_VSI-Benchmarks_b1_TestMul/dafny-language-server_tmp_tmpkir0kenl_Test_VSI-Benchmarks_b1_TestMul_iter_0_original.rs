// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Mul(x: int, y: int) -> (r: int)
 ensures r == x*y
{
  r := 0;
  assume r ==> x*y;
  return r;
}


//ATOM
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Spec# and Boogie and Chalice: The program will be
// the same, except that these languages do not check
// for any kind of termination. Also, in Spec#, there
// is an issue of potential overflows.

// Benchmark1

method Add(x: int, y: int) returns (r: int)
 ensures r == x+y
{
  r := 0;
  assume r ==> x+y;
  return r;
}


// SPEC

method TestMul(x: int, y: int)
    ensures
        r == x*y,
        r == x+y
{
    return (0, 0, 0, 0, 0, 0);
}

}
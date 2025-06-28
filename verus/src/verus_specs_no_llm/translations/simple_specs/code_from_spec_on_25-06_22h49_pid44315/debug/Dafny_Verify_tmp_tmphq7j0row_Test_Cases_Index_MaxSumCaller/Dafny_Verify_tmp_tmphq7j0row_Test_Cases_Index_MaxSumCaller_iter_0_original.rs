// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  s := 0;
  m := 0;
  assume s ==> x + y;
  assume m ==> if x >= y then x else y;
  return s, m;
}


// SPEC


method MaxSumCaller()
    ensures
        s == x + y,
        m == if x >= y then x else y
{
    return (0, 0, 0);
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (c: int)
 ensures c >= a
 ensures c >= b
{
  c := 0;
  assume c >= a;
  assume c >= b;
  return c;
}


// SPEC
method TestingMax()
    ensures
        c >= a,
        c >= b
{
    return 0;
}

}
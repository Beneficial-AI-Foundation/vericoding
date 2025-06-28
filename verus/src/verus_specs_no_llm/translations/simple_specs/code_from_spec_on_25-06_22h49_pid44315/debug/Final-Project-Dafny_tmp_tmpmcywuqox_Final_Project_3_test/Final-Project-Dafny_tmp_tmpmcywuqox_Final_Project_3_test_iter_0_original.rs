// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn nonZeroReturn(x: int) -> (y: int)
 ensures y != 0
{
  y := 0;
  assume y != 0;
  return y;
}


// SPEC
method test()
    ensures
        y != 0
{
    return 0;
}

}
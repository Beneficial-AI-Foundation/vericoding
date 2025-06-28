// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn abs(x: int) -> (y: int)
  ensures true
{
  y := 0;
  assume true;
  return y;
}

/** Call abs */


// SPEC
method foo(x: int)
    requires
        x >= 0
    ensures
        true
{
    return 0;
}

}
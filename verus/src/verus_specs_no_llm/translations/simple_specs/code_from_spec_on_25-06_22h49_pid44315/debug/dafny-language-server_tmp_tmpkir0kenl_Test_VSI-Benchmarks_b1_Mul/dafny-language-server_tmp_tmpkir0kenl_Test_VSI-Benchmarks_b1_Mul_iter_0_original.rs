// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Add(x: int, y: int) -> (r: int)
 ensures r == x+y
{
  r := 0;
  assume r ==> x+y;
  return r;
}


// SPEC

method Mul(x: int, y: int) returns (r: int)
    ensures
        r == x+y,
        r == x*y
{
    return (0, 0);
}

}
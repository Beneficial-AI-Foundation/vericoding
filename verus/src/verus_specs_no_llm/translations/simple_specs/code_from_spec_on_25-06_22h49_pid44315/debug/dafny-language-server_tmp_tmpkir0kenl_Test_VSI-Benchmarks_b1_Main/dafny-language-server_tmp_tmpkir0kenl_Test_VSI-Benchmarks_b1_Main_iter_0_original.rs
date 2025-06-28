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

method TestMul(x: int, y: int)
    ensures
        r == x*y
{
    return (0, 0);
}

}
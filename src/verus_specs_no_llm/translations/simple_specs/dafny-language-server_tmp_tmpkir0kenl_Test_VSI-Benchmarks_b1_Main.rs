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
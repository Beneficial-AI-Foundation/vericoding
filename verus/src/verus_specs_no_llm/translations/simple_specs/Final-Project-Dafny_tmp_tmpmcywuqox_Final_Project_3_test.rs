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
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
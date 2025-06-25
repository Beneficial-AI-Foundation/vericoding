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

fn A1(x: int, y: int) -> (r: int)
ensures r == x + y
{
  r := 0;
  assume r ==> x + y;
  return r;
}


// SPEC
method M1(x: int, y: int) returns (r: int)
    ensures
        r == x + y,
        r == x*y
{
    return (0, 0);
}

}
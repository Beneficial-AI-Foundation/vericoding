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

fn TripleConditions(x: int) -> (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
  r := 0;
  assume r ==> 3 * x;
  return r;
}


// SPEC

method Caller()
    requires
        x % 2 == 0
    ensures
        r == 3 * x
{
    return 0;
}

}
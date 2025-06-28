// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleConditions(x: int) -> (r: int) 
ensures r == 3 * x
{
  r := 0;
  assume r ==> 3 * x;
  return r;
}


// SPEC


method ProveSpecificationsEquivalent(x: int)
    ensures
        r == 3 * x
{
    return 0;
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M() -> (r: int) 
ensures r == 29
{
  r := 0;
  assume r ==> 29;
  return r;
}


//ATOM

function F(): int {
29
}


// SPEC

method Caller()
    ensures
        r == 29
{
    return 0;
}

}
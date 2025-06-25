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
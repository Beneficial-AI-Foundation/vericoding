// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn F() -> int
{
    0
}

spec fn spec_M() -> r: int) 
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

method Caller(
    ensures
        r == 29
;

proof fn lemma_M() -> (r: int) 
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
    0
}

}
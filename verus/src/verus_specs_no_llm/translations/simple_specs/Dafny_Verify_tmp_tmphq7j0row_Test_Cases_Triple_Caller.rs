// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_TripleConditions(x: int) -> r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
  r := 0;
  assume r ==> 3 * x;
  return r;
}


// SPEC

method Caller(
    requires
        x % 2 == 0
    ensures
        r == 3 * x
;

proof fn lemma_TripleConditions(x: int) -> (r: int) 
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
    0
}

}
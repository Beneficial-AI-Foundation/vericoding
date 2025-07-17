// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Add(x: int, y: int) -> r: int)
 ensures r == x+y
{
  r := 0;
  assume r ==> x+y;
  return r;
}


// SPEC

method Mul(x: int, y: int) returns (r: int
    ensures
        r == x+y,
        r == x*y
;

proof fn lemma_Add(x: int, y: int) -> (r: int)
 ensures r == x+y
{
  r := 0;
  assume r ==> x+y;
  return r;
}


// SPEC

method Mul(x: int, y: int) returns (r: int)
    ensures
        r == x+y,
        r == x*y
{
    (0, 0)
}

}
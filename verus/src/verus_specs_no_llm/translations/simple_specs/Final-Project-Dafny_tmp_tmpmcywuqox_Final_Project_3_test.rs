// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_nonZeroReturn(x: int) -> y: int)
 ensures y != 0
{
  y := 0;
  assume y != 0;
  return y;
}


// SPEC
method test(
    ensures
        y != 0
;

proof fn lemma_nonZeroReturn(x: int) -> (y: int)
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
    0
}

}
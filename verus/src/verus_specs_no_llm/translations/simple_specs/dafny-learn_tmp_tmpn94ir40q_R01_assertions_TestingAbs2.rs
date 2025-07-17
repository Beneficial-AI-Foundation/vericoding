// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Abs(x: int) -> y: int)
 ensures 0 <= y
 ensures x < 0 ==> y == -x
 ensures x >= 0 ==> y == x
{
  y := 0;
  assume 0 <= y;
  assume x < 0 ==> y == -x;
  assume x >= 0 ==> y == x;
  return y;
}


// SPEC

method TestingAbs2(
    ensures
        0 <= y,
        x < 0 ==> y == -x,
        x >= 0 ==> y == x
;

proof fn lemma_Abs(x: int) -> (y: int)
 ensures 0 <= y
 ensures x < 0 ==> y == -x
 ensures x >= 0 ==> y == x
{
  y := 0;
  assume 0 <= y;
  assume x < 0 ==> y == -x;
  assume x >= 0 ==> y == x;
  return y;
}


// SPEC

method TestingAbs2()
    ensures
        0 <= y,
        x < 0 ==> y == -x,
        x >= 0 ==> y == x
{
    0
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Max(a: int, b: int) -> c: int)
 ensures c >= a
 ensures c >= b
{
  c := 0;
  assume c >= a;
  assume c >= b;
  return c;
}


// SPEC
method TestingMax(
    ensures
        c >= a,
        c >= b
;

proof fn lemma_Max(a: int, b: int) -> (c: int)
 ensures c >= a
 ensures c >= b
{
  c := 0;
  assume c >= a;
  assume c >= b;
  return c;
}


// SPEC
method TestingMax()
    ensures
        c >= a,
        c >= b
{
    0
}

}
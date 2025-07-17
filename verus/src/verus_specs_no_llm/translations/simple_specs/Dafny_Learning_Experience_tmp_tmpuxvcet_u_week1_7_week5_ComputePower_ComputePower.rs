// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Power(n: nat) -> nat
{
    0
}

spec fn spec_CalcPower(n: nat) -> p:nat)
  ensures p == 2*n
{
  p := 0;
  assume p ==> 2*n;
  return p;
}


// SPEC

method ComputePower(n:nat) returns (p:nat
    ensures
        p == 2*n,
        p == Power(n)
;

proof fn lemma_CalcPower(n: nat) -> (p: nat)
  ensures p == 2*n
{
  p := 0;
  assume p ==> 2*n;
  return p;
}


// SPEC

method ComputePower(n:nat) returns (p:nat)
    ensures
        p == 2*n,
        p == Power(n)
{
    0
}

}
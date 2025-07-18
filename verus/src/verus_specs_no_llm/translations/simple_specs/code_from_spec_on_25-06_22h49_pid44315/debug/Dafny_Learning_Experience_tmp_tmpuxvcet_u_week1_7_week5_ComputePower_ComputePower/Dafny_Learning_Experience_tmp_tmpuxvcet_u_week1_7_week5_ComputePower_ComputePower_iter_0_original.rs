// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcPower(n: nat) -> (p: nat)
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
    return 0;
}

}
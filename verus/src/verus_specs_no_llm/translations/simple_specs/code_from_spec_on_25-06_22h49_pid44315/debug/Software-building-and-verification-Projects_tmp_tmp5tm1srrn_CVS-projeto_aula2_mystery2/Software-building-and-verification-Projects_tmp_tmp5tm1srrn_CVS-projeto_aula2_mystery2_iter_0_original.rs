// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mystery1(n: nat, m: nat) -> (res: nat)
 ensures n+m == res
{
  res := 0;
  assume n+m ==> res;
  return res;
}


// SPEC

method mystery2(n: nat, m: nat) returns (res: nat)
    ensures
        n+m == res,
        n*m == res
{
    return (0, 0);
}

}
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
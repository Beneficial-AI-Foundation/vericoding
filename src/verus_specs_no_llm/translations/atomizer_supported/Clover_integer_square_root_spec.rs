// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SquareRoot(N: nat) -> (r: nat)
    ensures r*r <= N < (r+1)*(r+1)
{
}

}
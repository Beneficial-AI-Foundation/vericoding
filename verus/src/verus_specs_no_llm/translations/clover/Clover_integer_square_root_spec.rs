// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquareRoot(N: nat) -> (r: nat)
    ensures
        r*r <= N < (r+1)*(r+1)
{
    return 0;
}

}
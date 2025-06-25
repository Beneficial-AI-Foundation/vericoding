// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountNeg(a: Vec<int>) -> (cnt: nat)
    ensures
        cnt == verifyNeg(a, a.len())
{
    return 0;
}

}
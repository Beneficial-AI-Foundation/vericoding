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

fn CountNeg(a: Vec<int>) -> (cnt: nat)
    ensures
        cnt == verifyNeg(a, a.len())
{
    return 0;
}

}
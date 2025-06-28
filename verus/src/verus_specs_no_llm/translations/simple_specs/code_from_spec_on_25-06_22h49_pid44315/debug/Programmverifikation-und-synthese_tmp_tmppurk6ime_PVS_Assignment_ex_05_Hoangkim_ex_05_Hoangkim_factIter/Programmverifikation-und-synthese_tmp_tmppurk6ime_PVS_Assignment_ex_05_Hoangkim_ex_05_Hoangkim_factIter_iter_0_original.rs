// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn factIter(n: nat) -> (a: nat)
    requires
        n >= 0
    ensures
        a == fact(n)
{
    return 0;
}

}
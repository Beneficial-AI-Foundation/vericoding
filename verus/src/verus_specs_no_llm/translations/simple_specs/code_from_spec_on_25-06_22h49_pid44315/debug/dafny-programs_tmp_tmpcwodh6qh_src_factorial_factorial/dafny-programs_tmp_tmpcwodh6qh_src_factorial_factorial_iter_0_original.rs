// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn factorial(n: nat) -> (res: nat)
    ensures
        res == fact(n)
{
    return 0;
}

}
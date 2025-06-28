// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sum(n: nat) -> (s: nat)
    ensures
        s == calcSum(n + 1)
{
    return 0;
}

}
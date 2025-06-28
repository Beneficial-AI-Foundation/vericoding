// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumUpTo(n: nat) -> (r: nat)
    ensures
        r == sum_up_to (n)
{
    return 0;
}

}
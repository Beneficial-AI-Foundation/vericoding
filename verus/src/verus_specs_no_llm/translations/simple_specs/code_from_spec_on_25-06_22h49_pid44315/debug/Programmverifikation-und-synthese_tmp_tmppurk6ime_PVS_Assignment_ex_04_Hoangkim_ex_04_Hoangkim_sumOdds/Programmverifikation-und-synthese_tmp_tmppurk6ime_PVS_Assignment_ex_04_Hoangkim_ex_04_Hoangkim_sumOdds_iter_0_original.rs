// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sumOdds(n: nat) -> (sum: nat)
    requires
        n > 0
    ensures
        sum == n * n
{
    return 0;
}

}
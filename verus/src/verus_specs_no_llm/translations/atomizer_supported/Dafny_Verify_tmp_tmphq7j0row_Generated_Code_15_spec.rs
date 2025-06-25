// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn main(n: int, k: int) -> (k_out: int)
    requires
        n > 0,
        k > n
    ensures
        k_out >= 0
{
    return 0;
}

}
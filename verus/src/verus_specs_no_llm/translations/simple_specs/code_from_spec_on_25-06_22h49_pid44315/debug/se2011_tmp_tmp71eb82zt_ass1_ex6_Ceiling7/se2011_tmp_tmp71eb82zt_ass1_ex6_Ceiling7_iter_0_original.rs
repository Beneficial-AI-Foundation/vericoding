// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    requires
        n >= 0
    ensures
        k == n-(n%7)
{
    return 0;
}

}
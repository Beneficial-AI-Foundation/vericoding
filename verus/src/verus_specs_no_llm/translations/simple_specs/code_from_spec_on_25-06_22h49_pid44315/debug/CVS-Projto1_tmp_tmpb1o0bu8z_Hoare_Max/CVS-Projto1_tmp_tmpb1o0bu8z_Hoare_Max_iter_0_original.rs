// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(x: nat, y: nat) -> (r: nat)
    ensures
        (r >= x && r >=y),
        (r == x || r == y)
{
    return 0;
}

}
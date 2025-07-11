// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Quotient(x: nat, y: nat) -> (r: int, q: int)
    requires
        y != 0
    ensures
        q * y + r == x && 0 <= r < y && 0 <= q
{
    return (0, 0);
}

}
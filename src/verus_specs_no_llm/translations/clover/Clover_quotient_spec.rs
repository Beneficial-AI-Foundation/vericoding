// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Quotient(x: nat, y: nat) -> r: int, q: int
    requires y != 0
    ensures q * y + r == x and 0 <= r < y and 0 <= q
{
}

}
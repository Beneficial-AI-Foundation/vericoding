// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Quotient(x: nat, y: nat) -> r:int, q:int
    requires
        y != 0
    ensures
        q * y + r == x && 0 <= r < y && 0 <= q
;

proof fn lemma_Quotient(x: nat, y: nat) -> (r: int, q: int)
    requires
        y != 0
    ensures
        q * y + r == x && 0 <= r < y && 0 <= q
{
    (0, 0)
}

}
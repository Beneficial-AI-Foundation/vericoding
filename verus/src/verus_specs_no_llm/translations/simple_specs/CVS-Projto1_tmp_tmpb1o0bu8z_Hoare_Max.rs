// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Max(x: nat, y: nat) -> r:nat
    ensures
        (r >= x && r >=y),
        (r == x || r == y)
;

proof fn lemma_Max(x: nat, y: nat) -> (r: nat)
    ensures
        (r >= x && r >=y),
        (r == x || r == y)
{
    0
}

}
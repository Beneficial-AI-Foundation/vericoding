// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Product(m: nat, n: nat) -> res:nat
    ensures
        res == m*n
;

proof fn lemma_Product(m: nat, n: nat) -> (res: nat)
    ensures
        res == m*n
{
    0
}

}
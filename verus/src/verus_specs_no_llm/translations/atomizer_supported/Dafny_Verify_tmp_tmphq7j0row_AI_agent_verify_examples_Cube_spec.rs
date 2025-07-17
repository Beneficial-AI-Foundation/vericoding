// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Cube(n: nat) -> c: nat
    ensures
        c == n * n * n
;

proof fn lemma_Cube(n: nat) -> (c: nat)
    ensures
        c == n * n * n
{
    0
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn f(n: nat) -> (nat)
{
    0
}

spec fn spec_mod(n: nat) -> a:nat
    ensures
        a == f(n)
;

proof fn lemma_mod(n: nat) -> (a: nat)
    ensures
        a == f(n)
{
    0
}

}
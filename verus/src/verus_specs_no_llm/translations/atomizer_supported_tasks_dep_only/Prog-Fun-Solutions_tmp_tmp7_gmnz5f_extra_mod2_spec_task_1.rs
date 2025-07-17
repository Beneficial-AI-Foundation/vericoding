// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn f2(n: nat) -> (nat)
{
    0
}

spec fn spec_mod2(n: nat) -> a:nat
    ensures
        a == f2(n)
;

proof fn lemma_mod2(n: nat) -> (a: nat)
    ensures
        a == f2(n)
{
    0
}

}
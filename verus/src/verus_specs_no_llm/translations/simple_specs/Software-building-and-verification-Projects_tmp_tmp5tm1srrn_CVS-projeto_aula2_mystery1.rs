// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mystery1(n: nat, m: nat) -> res: nat
    ensures
        n+m == res
;

proof fn lemma_mystery1(n: nat, m: nat) -> (res: nat)
    ensures
        n+m == res
{
    0
}

}
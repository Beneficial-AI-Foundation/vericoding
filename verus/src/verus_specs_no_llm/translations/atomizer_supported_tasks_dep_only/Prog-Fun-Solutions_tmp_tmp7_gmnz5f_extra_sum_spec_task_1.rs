// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn sum(n: nat) -> (int)
{
    0
}

spec fn spec_Sum(n: nat) -> s: int
    ensures
        s == sum(n)
;

proof fn lemma_Sum(n: nat) -> (s: int)
    ensures
        s == sum(n)
{
    0
}

}
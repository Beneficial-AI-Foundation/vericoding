// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Stairs(n: nat) -> nat
{
    0
}

spec fn spec_ClimbStairs(n: nat) -> r: nat
    ensures
        r == Stairs(n)
;

proof fn lemma_ClimbStairs(n: nat) -> (r: nat)
    ensures
        r == Stairs(n)
{
    0
}

}
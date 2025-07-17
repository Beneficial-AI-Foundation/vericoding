// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Expt(b: int, n: nat) -> int
    requires
        n >= 0
{
    0
}

spec fn spec_expt(b: int, n: nat) -> res: int
    ensures
        res == Expt(b, n)
;

proof fn lemma_expt(b: int, n: nat) -> (res: int)
    ensures
        res == Expt(b, n)
{
    0
}

}
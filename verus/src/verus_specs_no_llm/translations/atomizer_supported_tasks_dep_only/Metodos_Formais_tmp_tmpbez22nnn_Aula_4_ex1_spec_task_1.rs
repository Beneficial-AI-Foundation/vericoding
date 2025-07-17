// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Par(n: int) -> bool {
    n % 2 == 0
}

spec fn spec_FazAlgo(a: int, b: int) -> x:int, y:int
    requires
        a >= b && Par (a-b)
;

proof fn lemma_FazAlgo(a: int, b: int) -> (x: int, y: int)
    requires
        a >= b && Par (a-b)
{
    (0, 0)
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(x: int, y: int) -> x_out: int, y_out: int, n: int
    requires
        x >= 0,
        y >= 0,
        x == y
    ensures
        y_out == n
;

proof fn lemma_main(x: int, y: int) -> (x_out: int, y_out: int, n: int)
    requires
        x >= 0,
        y >= 0,
        x == y
    ensures
        y_out == n
{
    (0, 0, 0)
}

}
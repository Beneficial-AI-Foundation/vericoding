// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RotateLeftBits(n: u32, d: int) -> result: bv32
    requires
        0 <= d < 32
    ensures
        result == ((n << d) | (n >> (32 - d)))
;

proof fn lemma_RotateLeftBits(n: u32, d: int) -> (result: u32)
    requires
        0 <= d < 32
    ensures
        result == ((n << d) | (n >> (32 - d)))
{
    0
}

}
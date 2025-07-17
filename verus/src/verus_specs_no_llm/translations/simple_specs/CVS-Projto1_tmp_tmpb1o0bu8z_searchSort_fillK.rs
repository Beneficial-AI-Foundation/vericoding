// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_fillK(a: Vec<int>, n: int, k: int, c: int) -> b: bool
    requires
        0 <= c <= n,
        n == a.len()
;

proof fn lemma_fillK(a: Vec<int>, n: int, k: int, c: int) -> (b: bool)
    requires
        0 <= c <= n,
        n == a.len()
{
    false
}

}
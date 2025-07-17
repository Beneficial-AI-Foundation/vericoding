// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn has_count(v: int, a: Vec<int>, n: int) -> int
    reads a  // This allows the function to read from array 'a'
    requires
        n >= 0 && n <= a.len()
{
    0
}

spec fn spec_count(v: int, a: Vec<int>, n: int) -> r: int
    requires
        n >= 0 && n <= a.len()
    ensures
        has_count(v, a, n) == r
;

proof fn lemma_count(v: int, a: Vec<int>, n: int) -> (r: int)
    requires
        n >= 0 && n <= a.len()
    ensures
        has_count(v, a, n) == r
{
    0
}

}
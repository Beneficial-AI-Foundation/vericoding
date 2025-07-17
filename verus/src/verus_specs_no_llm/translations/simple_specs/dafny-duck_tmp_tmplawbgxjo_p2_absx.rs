// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> nat
{
    0
}

spec fn spec_absx(x: Vec<int>) -> y:array<int>
    ensures
        y.len() == x.len(),
        forall |i: int| 0 <= i < y.len() ==> y.index(i) == abs(x.index(i))
;

proof fn lemma_absx(x: Vec<int>) -> (y: Vec<int>)
    ensures
        y.len() == x.len(),
        forall |i: int| 0 <= i < y.len() ==> y.index(i) == abs(x.index(i))
{
    Vec::new()
}

}
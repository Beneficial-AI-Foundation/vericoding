// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(a: int) -> nat
{
    0
}

spec fn spec_aba(a: Vec<int>) -> b:array<int>
    ensures
        a.len() == b.len() // needed for next line,
        forall |x: int| 0<=x<b.len() ==> b.index(x) == abs(a.index(x))
;

proof fn lemma_aba(a: Vec<int>) -> (b: Vec<int>)
    ensures
        a.len() == b.len() // needed for next line,
        forall |x: int| 0<=x<b.len() ==> b.index(x) == abs(a.index(x))
{
    Vec::new()
}

}
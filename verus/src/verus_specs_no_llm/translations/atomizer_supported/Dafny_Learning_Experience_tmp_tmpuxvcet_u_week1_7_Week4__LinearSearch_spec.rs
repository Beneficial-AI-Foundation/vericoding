// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn P(n: int) -> bool {
    n % 2 == 0
}

spec fn spec_TestLinearSearch() {
}


// SPEC 

method LinearSeach1<T>(a: Vec<T>, P: T -> bool) -> n: int
    ensures
        0 <= n <= a.len(),
        n == a.len() || P(a.index(n)),
        n == a.len() ==> forall |i: int| 0 <= i < a.len() ==> !P(a.index(i))
;

proof fn lemma_TestLinearSearch() {
}


// SPEC 

method LinearSeach1<T>(a: Vec<T>, P: T -> bool) -> (n: int)
    ensures
        0 <= n <= a.len(),
        n == a.len() || P(a.index(n)),
        n == a.len() ==> forall |i: int| 0 <= i < a.len() ==> !P(a.index(i))
{
    0
}

}
// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn P(n: int) -> bool {
    n % 2 == 0
}

fn TestLinearSearch() {
}


// SPEC 

method LinearSeach1<T>(a: Vec<T>, P: T -> bool) -> (n: int)
    ensures
        0 <= n <= a.len(),
        n == a.len() || P(a.spec_index(n)),
        n == a.len() ==> forall i :: 0 <= i < a.len() ==> !P(a.spec_index(i))
{
    return 0;
}

}
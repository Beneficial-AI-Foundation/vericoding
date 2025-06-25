// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn P(n: int) -> bool {
    n % 2 == 0
}

fn TestLinearSearch() {
}


// SPEC 

method LinearSeach1<T>(a: Vec<T>, P: T -> bool) -> (n: int)
    ensures 0 <= n <= a.len(),
            n == a.len() or P(a[n]),
            n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> !P(a[i])
{
}

}
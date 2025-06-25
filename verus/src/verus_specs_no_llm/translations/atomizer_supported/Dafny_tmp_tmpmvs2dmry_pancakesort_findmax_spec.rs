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

fn findMax(a: Vec<int>, n: int) -> (r: int)
    requires
        a.len() > 0,
        0 < n <= a.len()
    ensures
        0 <= r < n <= a.len(),
        forall k :: 0 <= k < n <= a.len() ==> a.spec_index(r) >= a.spec_index(k),
        multiset(a.spec_index(..)) == multiset(old(a.spec_index(..)))
{
    return 0;
}

}
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

fn NoDups(a: Vec<int>) -> (noDups: bool)
    requires
        forall j : int :: 0 < j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j) // a sorted
    ensures
        noDups <==> forall j : int :: 1 <= j < a.len() ==> a.spec_index(j-1) != a.spec_index(j)
{
    return false;
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NoDups(a: Vec<int>) -> (noDups: bool)
    requires
        forall |j: int| 0 < j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j) // a sorted
    ensures
        noDups <==> (forall |j: int| 1 <= j < a.len() ==> a.spec_index(j-1) != a.spec_index(j))
{
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall |j: int| 1 <= j < i ==> a.spec_index(j-1) != a.spec_index(j)
    {
        if a[i-1] == a[i] {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}
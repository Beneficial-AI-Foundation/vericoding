use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn no_dups(a: Vec<int>) -> (no_dups: bool)
    requires
        forall |j: int| 0 < j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j) // a sorted
    ensures
        no_dups <==> (forall |j: int| 1 <= j < a.len() ==> a.spec_index(j-1) != a.spec_index(j))
{
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall |j: int| 1 <= j < i ==> a.spec_index(j-1) != a.spec_index(j)
    {
        if a.spec_index((i-1) as int) == a.spec_index(i as int) {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}
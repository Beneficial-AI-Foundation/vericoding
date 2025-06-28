use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn no_dups(a: Vec<int>) -> (result: bool)
    requires
        forall |j: int| 0 < j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j) // a sorted
    ensures
        result <==> (forall |j: int| 1 <= j < a.len() ==> a.spec_index(j-1) != a.spec_index(j))
{
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall |j: int| 1 <= j < i ==> a.spec_index(j-1) != a.spec_index(j)
        decreases a.len() - i
    {
        if a.spec_index((i-1) as int) == a.spec_index(i as int) {
            return false;
        }
        i = i + 1;
    }
    true
}

}
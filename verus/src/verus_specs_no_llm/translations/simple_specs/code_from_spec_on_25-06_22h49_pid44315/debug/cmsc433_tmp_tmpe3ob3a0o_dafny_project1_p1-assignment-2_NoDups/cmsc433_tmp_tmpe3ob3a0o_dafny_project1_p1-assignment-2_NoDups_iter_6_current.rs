use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn no_dups(a: Vec<int>) -> (result: bool)
    requires
        forall |j: int| 0 <= j < a.len() - 1 ==> a.spec_index(j) <= a.spec_index(j+1) // a sorted
    ensures
        result <==> (forall |j: int| 0 <= j < a.len() - 1 ==> a.spec_index(j) != a.spec_index(j+1))
{
    if a.len() <= 1 {
        return true;
    }
    
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a.len() >= 2,
            forall |j: int| 0 <= j < (i as int) - 1 ==> a.spec_index(j) != a.spec_index(j+1)
        decreases a.len() - i
    {
        if a.spec_index((i-1) as int) == a.spec_index(i as int) {
            return false;
        }
        i = i + 1;
    }
    
    // At this point, i == a.len() and we've checked all consecutive pairs
    assert(forall |j: int| 0 <= j < a.len() - 1 ==> a.spec_index(j) != a.spec_index(j+1));
    true
}

}
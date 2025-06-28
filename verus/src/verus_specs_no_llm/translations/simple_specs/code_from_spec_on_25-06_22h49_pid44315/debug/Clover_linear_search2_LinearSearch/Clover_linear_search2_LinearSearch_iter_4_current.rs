use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    requires
        exists|i: int| 0<=i<a.len() && a.spec_index(i)==e
    ensures
        0<=n<a.len() && a.spec_index(n)==e,
        forall|k: int| 0 <= k < n ==> a.spec_index(k)!=e
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) != e,
            exists|j: int| i <= j < a.len() && a.spec_index(j) == e
    {
        if a[i] == e {
            assert(a.spec_index(i as int) == e);
            assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) != e);
            return i as int;
        }
        i = i + 1;
    }
    
    // This point should never be reached due to the loop invariant
    // The invariant guarantees that there exists j with i <= j < a.len() such that a[j] == e
    // But when we exit the loop, i == a.len(), so there's no such j
    // This is a contradiction, so this point is unreachable
    assert(i == a.len());
    assert(exists|j: int| i <= j < a.len() && a.spec_index(j) == e);
    assert(forall|j: int| !(i <= j < a.len()));
    assert(false);
    0
}

}
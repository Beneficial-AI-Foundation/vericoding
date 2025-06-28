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
            exists|j: int| 0 <= j < a.len() && a.spec_index(j) == e
    {
        if a[i] == e {
            return i as int;
        }
        i = i + 1;
    }
    
    // This point should never be reached due to the precondition
    // The precondition guarantees that there exists an element equal to e
    // But the loop invariant says we haven't found it yet in positions 0..i
    // Since i == a.len() now, we've checked all positions without finding e
    // This contradicts the precondition
    assert(false);
    0
}

}
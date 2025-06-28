use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    requires
        exists i::0<=i<a.len() && a.spec_index(i)==e
    ensures
        0<=n<a.len() && a.spec_index(n)==e,
        forall k :: 0 <= k < n ==> a.spec_index(k)!=e
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall k :: 0 <= k < i ==> a.spec_index(k) != e,
            exists j :: 0 <= j < a.len() && a.spec_index(j) == e
    {
        if a[i] == e {
            return i as int;
        }
        i = i + 1;
    }
    
    // This point should never be reached due to the precondition
    // but we need to satisfy the compiler
    0
}

}
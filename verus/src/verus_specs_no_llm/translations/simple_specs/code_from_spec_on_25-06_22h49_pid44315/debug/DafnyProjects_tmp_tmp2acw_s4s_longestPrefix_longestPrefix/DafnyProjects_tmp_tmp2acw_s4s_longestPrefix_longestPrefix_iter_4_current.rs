use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longestPrefix(a: Vec<int>, b: &[int]) -> (i: usize)
    ensures
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i] != b[i]
{
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len() && a[i] == b[i]
        invariant
            i <= a.len() && i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
            // Add invariant to help prove the postcondition
            forall |j: int| 0 <= j < i ==> a[j] == b[j]
    {
        i = i + 1;
    }
    
    // The loop exits when either:
    // 1. i >= a.len() OR i >= b.len() OR a[i] != b[i]
    // This automatically satisfies the third postcondition
    
    i
}

}
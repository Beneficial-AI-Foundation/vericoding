use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMax(a: Vec<int>) -> (max_idx: nat)
    requires
        a.len() > 0
    ensures
        0 <= max_idx < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a.spec_index(max_idx as int) >= a.spec_index(j)
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= i <= a.len(),
            max_idx < i,
            forall|j: int| 0 <= j < i ==> a.spec_index(max_idx as int) >= a.spec_index(j)
    {
        if a.spec_index(i as int) > a.spec_index(max_idx as int) {
            max_idx = i;
        }
        i = i + 1;
    }
    
    // Proof that the postcondition holds
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(max_idx as int) >= a.spec_index(j)) by {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < i ==> a.spec_index(max_idx as int) >= a.spec_index(j));
    };
    
    max_idx as nat
}

}

The key changes I made:



The algorithm works correctly:
- We start with `max_idx = 0` and `i = 1`
- In each iteration, if `a[i] > a[max_idx]`, we update `max_idx = i`
- Then we increment `i`, so `max_idx < i` is maintained
- The loop invariant ensures `max_idx` always points to the maximum among elements `0..i`
- When the loop ends, `i == a.len()`, so `max_idx` points to the maximum among all elements
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMax(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        0 <= max < a.len(),
        forall|x: int| 0 <= x < a.len() ==> a.spec_index(max) >= a.spec_index(x)
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(max_idx as int) >= a.spec_index(j),
            a.len() > 0
    {
        if a.spec_index(i as int) > a.spec_index(max_idx as int) {
            max_idx = i;
        }
        i = i + 1;
    }
    
    // After the loop, we need to prove that max_idx is indeed the maximum
    // The loop invariant gives us that max_idx is maximum among indices 0..i
    // Since i == a.len() after the loop, max_idx is maximum among all indices
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(max_idx as int) >= a.spec_index(j));
    
    max_idx as int
}

}
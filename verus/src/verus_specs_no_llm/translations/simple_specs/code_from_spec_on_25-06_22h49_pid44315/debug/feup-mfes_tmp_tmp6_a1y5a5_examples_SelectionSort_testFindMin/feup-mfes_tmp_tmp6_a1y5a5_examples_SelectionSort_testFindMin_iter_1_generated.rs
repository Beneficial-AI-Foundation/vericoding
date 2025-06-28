use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
    requires 
        0 <= from < to <= a.len()
    ensures 
        from <= index < to,
        forall|k: nat| from <= k < to ==> a.spec_index(k as int) >= a.spec_index(index as int)
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: nat| from <= k < i ==> a.spec_index(k as int) >= a.spec_index(min_index as int)
    {
        if a.spec_index(i as int) < a.spec_index(min_index as int) {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

// Test method
method testFindMin() {
    let a = vec![3.0, 1.0, 4.0, 1.0, 5.0];
    let from = 0;
    let to = 5;
    
    let index = findMin(a, from, to);
    
    assert(from <= index < to);
    assert(forall|k: nat| from <= k < to ==> a.spec_index(k as int) >= a.spec_index(index as int));
}

}
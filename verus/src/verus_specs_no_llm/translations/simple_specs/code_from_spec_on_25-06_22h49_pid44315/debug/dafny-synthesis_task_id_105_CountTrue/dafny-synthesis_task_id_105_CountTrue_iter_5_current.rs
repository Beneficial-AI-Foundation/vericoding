use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to count true values up to index i
spec fn countTo(a: Vec<bool>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else if i > a.len() {
        countTo(a, a.len())
    } else {
        countTo(a, i - 1) + if a[i - 1] { 1 } else { 0 }
    }
}

fn CountTrue(a: Vec<bool>) -> (result: usize)
    ensures
        result == countTo(a, a.len() as int)
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == countTo(a, i as int)
    {
        proof {
            // Before updating, establish that the current invariant holds
            assert(count == countTo(a, i as int));
            assert(i < a.len());
        }
        
        if a[i] {
            count = count + 1;
        }
        i = i + 1;
        
        proof {
            // After updating, prove the invariant holds for the new values
            let old_i = (i - 1) as int;
            let new_i = i as int;
            
            // Key insight: countTo(a, new_i) = countTo(a, old_i) + contribution of a[old_i]
            assert(old_i == (i - 1) as int);
            assert(new_i == old_i + 1);
            assert(old_i >= 0);
            assert(new_i <= a.len());
            
            // By definition of countTo
            assert(countTo(a, new_i) == countTo(a, old_i) + if a[old_i] { 1 } else { 0 });
            
            // We know count was updated correctly
            if a[old_i] {
                assert(count == countTo(a, old_i) + 1);
                assert(countTo(a, new_i) == countTo(a, old_i) + 1);
            } else {
                assert(count == countTo(a, old_i));
                assert(countTo(a, new_i) == countTo(a, old_i));
            }
            
            // Therefore the invariant holds
            assert(count == countTo(a, new_i));
        }
    }
    
    count
}

fn main() {
}

}
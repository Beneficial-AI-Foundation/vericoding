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
        let old_count = count;
        let old_i = i;
        
        if a[i] {
            count = count + 1;
        }
        i = i + 1;
        
        proof {
            // Prove the invariant holds after the update
            assert(old_i < a.len());
            assert(i == old_i + 1);
            assert(old_i as int + 1 == i as int);
            
            // By definition of countTo:
            // countTo(a, i as int) = countTo(a, old_i as int + 1) 
            //                      = countTo(a, old_i as int) + (if a[old_i] then 1 else 0)
            assert(countTo(a, i as int) == countTo(a, old_i as int) + if a[old_i as int] { 1 } else { 0 });
            
            // We know from the invariant that old_count == countTo(a, old_i as int)
            assert(old_count == countTo(a, old_i as int));
            
            // Now we need to show that count == countTo(a, i as int)
            if a[old_i] {
                assert(count == old_count + 1);
                assert(a[old_i as int]);
                assert(countTo(a, i as int) == countTo(a, old_i as int) + 1);
                assert(count == countTo(a, i as int));
            } else {
                assert(count == old_count);
                assert(!a[old_i as int]);
                assert(countTo(a, i as int) == countTo(a, old_i as int) + 0);
                assert(countTo(a, i as int) == countTo(a, old_i as int));
                assert(count == countTo(a, i as int));
            }
        }
    }
    
    count
}

fn main() {
}

}
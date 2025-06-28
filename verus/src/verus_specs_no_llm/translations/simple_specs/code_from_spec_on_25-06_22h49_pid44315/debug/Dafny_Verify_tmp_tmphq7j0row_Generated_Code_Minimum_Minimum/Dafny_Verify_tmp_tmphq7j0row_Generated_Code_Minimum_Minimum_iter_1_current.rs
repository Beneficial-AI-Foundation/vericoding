use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Minimum(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        exists i :: 0 <= i < a.len() && m == a.spec_index(i),
        forall i :: 0 <= i < a.len() ==> m <= a.spec_index(i)
{
    let mut min = a[0];
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            exists i :: 0 <= i < a.len() && min == a.spec_index(i),
            forall i :: 0 <= i < idx ==> min <= a.spec_index(i)
    {
        if a[idx] < min {
            min = a[idx];
        }
        idx = idx + 1;
    }
    
    min
}

}

The implementation:

   - `idx` stays within bounds
   - `min` is always an element from the vector (exists property)
   - `min` is less than or equal to all elements checked so far

The loop invariants are crucial for verification - they maintain that the minimum candidate is always an actual element from the vector and is indeed minimal among all elements examined so far.
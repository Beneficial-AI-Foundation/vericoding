use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minArray(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        forall|k| 0 <= k < a.len() ==> m <= a.spec_index(k),
        exists|k| 0 <= k < a.len() && m == a.spec_index(k)
{
    let mut min = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k| 0 <= k < i ==> min <= a.spec_index(k),
            exists|k| 0 <= k < i && min == a.spec_index(k)
    {
        if a[i as int] < min {
            min = a[i as int];
            proof {
                // After updating min, we need to prove the invariant holds
                // min is now a[i], so the existence part is satisfied with k = i
                assert(min == a.spec_index(i as int));
                assert(exists|k| 0 <= k <= i && min == a.spec_index(k));
            }
        }
        i = i + 1;
    }
    
    min
}

}
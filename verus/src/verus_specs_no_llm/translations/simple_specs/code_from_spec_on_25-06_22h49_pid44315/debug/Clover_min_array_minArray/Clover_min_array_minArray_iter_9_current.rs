use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minArray(a: Vec<i32>) -> (r: i32)
    requires
        a.len() > 0
    ensures
        forall|i: int| 0 <= i < a.len() ==> r <= a.spec_index(i),
        exists|i: int| 0 <= i < a.len() && r == a.spec_index(i)
{
    let mut min = a[0];
    let mut idx: usize = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|j: int| 0 <= j < idx ==> min <= a.spec_index(j),
            exists|j: int| 0 <= j < idx && min == a.spec_index(j)
    {
        if a[idx] < min {
            min = a[idx];
            proof {
                assert(min == a.spec_index(idx as int));
                assert(0 <= idx < a.len());
            }
        }
        idx += 1;
        
        proof {
            assert(forall|j: int| 0 <= j < (idx - 1) ==> min <= a.spec_index(j));
            if a.spec_index((idx - 1) as int) < min {
                assert(min == a.spec_index((idx - 1) as int));
            }
            assert(min <= a.spec_index((idx - 1) as int));
            assert(forall|j: int| 0 <= j < idx ==> min <= a.spec_index(j));
        }
    }
    
    proof {
        assert(idx == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> min <= a.spec_index(j));
        assert(exists|j: int| 0 <= j < a.len() && min == a.spec_index(j));
    }
    
    min
}

}
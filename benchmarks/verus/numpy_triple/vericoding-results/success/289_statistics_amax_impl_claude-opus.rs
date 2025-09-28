// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn amax(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        (exists|max_idx: int| 0 <= max_idx < a.len() &&
            result as int == a@[max_idx] as int &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] as int <= result as int)) &&
        (exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result as int == a@[first_max_idx] as int &&
            (forall|i: int| 0 <= i < a.len() && a@[i] as int == result as int ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] as int <= result as int)) &&
        ((forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] as int == a@[j] as int) ==> 
            result as int == a@[0] as int) &&
        (exists|witness: int| 0 <= witness < a.len() && result as int == a@[witness] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added assertions to help verify all postconditions */
    let mut max = a[0];
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= max_idx < i,
            max as int == a@[max_idx as int] as int,
            forall|j: int| 0 <= j < i ==> a@[j] as int <= max as int,
            forall|j: int| 0 <= j < i && a@[j] as int == max as int ==> max_idx as int <= j,
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
            max_idx = i;
        }
        i = i + 1;
    }
    
    proof {
        assert(0 <= max_idx < a.len());
        assert(max as int == a@[max_idx as int] as int);
        assert(forall|j: int| 0 <= j < a.len() ==> a@[j] as int <= max as int);
        assert(exists|idx: int| 0 <= idx < a.len() && max as int == a@[idx] as int);
        assert(exists|first_idx: int| 0 <= first_idx < a.len() && max as int == a@[first_idx] as int && (forall|j: int| 0 <= j < a.len() && a@[j] as int == max as int ==> first_idx <= j));
    }
    
    max
}
// </vc-code>

}
fn main() {}
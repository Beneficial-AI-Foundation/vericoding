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
    /* code modified by LLM (iteration 3): Changed loop variables to usize to fix compilation error with 'int' in execution code */
    let mut max_val: i8 = a[0];
    let mut first_max_idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= (i as int) <= (a.len() as int),
            0 <= (first_max_idx as int) < (i as int),
            max_val as int == a@[(first_max_idx as int)] as int,
            (forall|j: int| 0 <= j < (i as int) ==> a@[j] as int <= max_val as int),
            (forall|j: int| 0 <= j < (i as int) && a@[j] as int == max_val as int ==> (first_max_idx as int) <= j),
        decreases (a.len() - i) as int,
    {
        let current = a[i as usize];
        if current > max_val {
            max_val = current;
            first_max_idx = i;
        }
        i += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}
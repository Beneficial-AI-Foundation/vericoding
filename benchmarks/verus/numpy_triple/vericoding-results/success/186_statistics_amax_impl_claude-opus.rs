// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn amax(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        (exists|max_idx: int| 0 <= max_idx < a.len() &&
            result == a@[max_idx] &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] <= result)) &&
        (exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result == a@[first_max_idx] &&
            (forall|i: int| 0 <= i < a.len() && a@[i] == result ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] <= result)) &&
        ((forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] == a@[j]) ==> 
            result == a@[0]) &&
        (exists|witness: int| 0 <= witness < a.len() && result == a@[witness])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut max = a[0];
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= max_idx < i,
            max == a@[max_idx as int],
            forall|j: int| 0 <= j < i ==> a@[j] <= max,
            forall|j: int| 0 <= j < i && a@[j] == max ==> max_idx as int <= j,
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
            max_idx = i;
        }
        i = i + 1;
    }
    
    max
}
// </vc-code>

}
fn main() {}
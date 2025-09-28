// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    requires
        lists.len() > 0,
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut min_length = lists[0].len();
    let mut i: usize = 1;
    
    while i < lists.len()
        invariant
            0 < i <= lists.len(),
            exists|j: int| #![auto] 0 <= j < i && min_length == lists[j].len(),
            forall|j: int| #![auto] 0 <= j < i ==> min_length <= lists[j].len(),
        decreases lists.len() - i
    {
        if lists[i].len() < min_length {
            min_length = lists[i].len();
        }
        i = i + 1;
    }
    
    min_length
}
// </vc-code>

}
fn main() {}
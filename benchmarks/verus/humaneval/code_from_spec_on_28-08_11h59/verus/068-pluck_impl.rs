use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        nodes@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 0 ==> forall|i: int| 0 <= i < nodes@.len() ==> nodes@[i] % 2 != 0,
        result@.len() == 2 ==> {
            let node = result@[0];
            let index = result@[1];
            &&& 0 <= index < nodes@.len()
            &&& nodes@[index as int] == node
            &&& node % 2 == 0
            &&& forall|i: int|
                0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i] && forall|i: int|
                    0 <= i < result@[1] ==> nodes@[i] % 2 != 0 || nodes@[i] > node
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut smallest_even: Option<u32> = None;
    let mut smallest_index: Option<usize> = None;
    
    let mut i = 0;
    while i < nodes.len()
        invariant
            0 <= i <= nodes.len(),
            smallest_even.is_some() ==> smallest_index.is_some(),
            smallest_index.is_some() ==> smallest_even.is_some(),
            smallest_index.is_some() ==> {
                let idx = smallest_index.unwrap();
                &&& idx < i
                &&& idx < nodes@.len()
                &&& nodes@[idx as int] == smallest_even.unwrap()
                &&& smallest_even.unwrap() % 2 == 0
            },
            smallest_even.is_some() ==> {
                let val = smallest_even.unwrap();
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> val <= nodes@[j]
            },
            smallest_even.is_none() ==> forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
            smallest_index.is_some() ==> {
                let idx = smallest_index.unwrap();
                let val = smallest_even.unwrap();
                forall|j: int| 0 <= j < idx ==> nodes@[j] % 2 != 0 || nodes@[j] > val
            },
        decreases nodes.len() - i
    {
        if nodes[i] % 2 == 0 {
            if smallest_even.is_none() || nodes[i] < smallest_even.unwrap() {
                smallest_even = Some(nodes[i]);
                smallest_index = Some(i);
            } else if nodes[i] == smallest_even.unwrap() {
                let current_idx = smallest_index.unwrap();
                if i < current_idx {
                    smallest_index = Some(i);
                }
            }
        }
        i += 1;
    }
    
    if let (Some(val), Some(idx)) = (smallest_even, smallest_index) {
        vec![val, idx as u32]
    } else {
        vec![]
    }
}
// </vc-code>

}
fn main() {}
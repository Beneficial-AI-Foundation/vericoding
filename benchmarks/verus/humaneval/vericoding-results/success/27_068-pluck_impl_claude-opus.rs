// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)

    requires
        nodes@.len() <= u32::MAX,

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
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut smallest_even: Option<u32> = None;
    let mut smallest_index: Option<usize> = None;
    
    let mut i: usize = 0;
    while i < nodes.len()
        invariant
            i <= nodes.len(),
            smallest_even.is_none() <==> smallest_index.is_none(),
            smallest_even.is_some() ==> {
                let val = smallest_even.unwrap();
                let idx = smallest_index.unwrap();
                &&& 0 <= idx < i
                &&& idx < nodes.len()
                &&& nodes@[idx as int] == val
                &&& val % 2 == 0
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> val <= nodes@[j]
                &&& forall|j: int| 0 <= j < idx ==> nodes@[j] % 2 != 0 || nodes@[j] > val
            },
            smallest_even.is_none() ==> forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
        decreases nodes.len() - i
    {
        if nodes[i] % 2 == 0 {
            if smallest_even.is_none() || nodes[i] < smallest_even.unwrap() {
                smallest_even = Some(nodes[i]);
                smallest_index = Some(i);
            }
        }
        i = i + 1;
    }
    
    if smallest_even.is_some() {
        let mut result = Vec::new();
        result.push(smallest_even.unwrap());
        result.push(smallest_index.unwrap() as u32);
        result
    } else {
        Vec::new()
    }
}
// </vc-code>

}
fn main() {}
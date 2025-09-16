// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause */
spec fn has_even(nodes: Seq<u32>) -> bool {
    exists|i: int| 0 <= i < nodes.len() && nodes[i] % 2 == 0
}

spec fn is_smallest_even_at(nodes: Seq<u32>, value: u32, index: int) -> bool {
    &&& 0 <= index < nodes.len()
    &&& nodes[index] == value
    &&& value % 2 == 0
    &&& forall|i: int| 0 <= i < nodes.len() && nodes[i] % 2 == 0 ==> value <= nodes[i]
    &&& forall|i: int| 0 <= i < index ==> nodes[i] % 2 != 0 || nodes[i] > value
}
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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut smallest_even: Option<u32> = None;
    let mut smallest_index: Option<usize> = None;
    
    let mut i = 0;
    while i < nodes.len()
        invariant
            0 <= i <= nodes.len(),
            smallest_even.is_some() == smallest_index.is_some(),
            smallest_even.is_some() ==> {
                let val = smallest_even.unwrap();
                let idx = smallest_index.unwrap();
                &&& idx < i
                &&& nodes@[idx as int] == val
                &&& val % 2 == 0
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> val <= nodes@[j]
                &&& forall|j: int| 0 <= j < idx ==> nodes@[j] % 2 != 0 || nodes@[j] > val
            },
            smallest_even.is_none() ==> forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
        decreases nodes.len() - i
    {
        let current = nodes[i];
        if current % 2 == 0 {
            match smallest_even {
                None => {
                    smallest_even = Some(current);
                    smallest_index = Some(i);
                }
                Some(val) => {
                    if current < val {
                        smallest_even = Some(current);
                        smallest_index = Some(i);
                    }
                }
            }
        }
        i += 1;
    }
    
    match (smallest_even, smallest_index) {
        (Some(val), Some(idx)) => {
            vec![val, idx as u32]
        }
        _ => {
            vec![]
        }
    }
}
// </vc-code>

}
fn main() {}
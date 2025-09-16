// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added condition for indices before found index */
fn find_smallest_even(nodes: &Vec<u32>) -> (result: Option<(u32, usize)>)
    requires
        nodes@.len() <= u32::MAX,
    ensures
        match result {
            Some((val, idx)) => {
                &&& 0 <= idx < nodes@.len()
                &&& nodes@[idx as int] == val
                &&& val % 2 == 0
                &&& forall|i: int| 0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> val <= nodes@[i]
                &&& forall|i: int| 0 <= i < idx ==> nodes@[i] % 2 != 0 || nodes@[i] > val
            }
            None => forall|i: int| 0 <= i < nodes@.len() ==> nodes@[i] % 2 != 0,
        }
{
    let mut min_even: Option<u32> = None;
    let mut min_index: Option<usize> = None;
    
    for i in 0..nodes.len()
        invariant
            0 <= i <= nodes@.len(),
            match min_even {
                Some(val) => {
                    &&& min_index.is_some()
                    &&& 0 <= min_index.unwrap() < i
                    &&& nodes@[min_index.unwrap() as int] == val
                    &&& val % 2 == 0
                    &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> val <= nodes@[j]
                    &&& forall|j: int| 0 <= j < min_index.unwrap() ==> nodes@[j] % 2 != 0 || nodes@[j] > val
                }
                None => forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
            }
    {
        let x = nodes[i];
        if x % 2 == 0 {
            match min_even {
                None => {
                    min_even = Some(x);
                    min_index = Some(i);
                }
                Some(current_min) => {
                    if x < current_min {
                        min_even = Some(x);
                        min_index = Some(i);
                    }
                }
            }
        }
    }
    
    match min_even {
        None => None,
        Some(val) => Some((val, min_index.unwrap())),
    }
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
/* code modified by LLM (iteration 3): no change, using updated helper */
{
    let result = find_smallest_even(nodes);
    match result {
        None => Vec::new(),
        Some((val, idx)) => {
            vec![val, idx as u32]
        }
    }
}
// </vc-code>

}
fn main() {}
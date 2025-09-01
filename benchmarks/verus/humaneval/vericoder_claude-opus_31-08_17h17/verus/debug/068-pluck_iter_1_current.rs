use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    let mut min_even: Option<u32> = None;
    let mut min_index: Option<u32> = None;
    
    let mut i: usize = 0;
    while i < nodes.len()
        invariant
            i <= nodes.len(),
            min_even.is_none() <==> min_index.is_none(),
            min_even.is_some() ==> {
                let val = min_even.unwrap();
                let idx = min_index.unwrap();
                &&& 0 <= idx < i
                &&& nodes@[idx as int] == val
                &&& val % 2 == 0
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> val <= nodes@[j]
                &&& forall|j: int| 0 <= j < idx ==> nodes@[j] % 2 != 0 || nodes@[j] > val
            },
            min_even.is_none() ==> forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
    {
        if nodes[i] % 2 == 0 {
            match min_even {
                None => {
                    min_even = Some(nodes[i]);
                    min_index = Some(i as u32);
                },
                Some(current_min) => {
                    if nodes[i] < current_min {
                        min_even = Some(nodes[i]);
                        min_index = Some(i as u32);
                    }
                }
            }
        }
        i = i + 1;
    }
    
    match min_even {
        None => vec![],
        Some(val) => {
            let idx = min_index.unwrap();
            vec![val, idx]
        }
    }
}
// </vc-code>

fn main() {}
}
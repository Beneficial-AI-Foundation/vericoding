use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_smallest_even_properties(nodes: Seq<u32>, smallest_even: u32, smallest_index: int)
    requires
        0 <= smallest_index < nodes.len(),
        nodes[smallest_index] == smallest_even,
        smallest_even % 2 == 0,
        forall|i: int| 0 <= i < nodes.len() && nodes[i] % 2 == 0 ==> smallest_even <= nodes[i],
        forall|i: int| 0 <= i < smallest_index ==> nodes[i] % 2 != 0 || nodes[i] > smallest_even,
    ensures
        forall|i: int| 0 <= i < smallest_index ==> nodes[i] % 2 != 0 || nodes[i] > smallest_even,
{}

proof fn lemma_no_even_exists(nodes: Seq<u32>)
    requires
        forall|i: int| 0 <= i < nodes.len() ==> nodes[i] % 2 != 0,
    ensures
        forall|i: int| 0 <= i < nodes.len() ==> nodes[i] % 2 != 0,
{}
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
    
    let mut i = 0usize;
    while i < nodes.len()
        invariant
            i <= nodes.len(),
            smallest_even.is_some() == smallest_index.is_some(),
            smallest_even.is_some() ==> {
                let even_val = smallest_even.unwrap();
                let even_idx = smallest_index.unwrap();
                &&& even_idx < i
                &&& even_idx < nodes.len()
                &&& nodes@[even_idx as int] == even_val
                &&& even_val % 2 == 0
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> even_val <= nodes@[j]
                &&& forall|j: int| 0 <= j < even_idx ==> nodes@[j] % 2 != 0 || nodes@[j] > even_val
            },
            smallest_even.is_none() ==> forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
    {
        if nodes[i] % 2 == 0 {
            match smallest_even {
                None => {
                    smallest_even = Some(nodes[i]);
                    smallest_index = Some(i);
                },
                Some(current_smallest) => {
                    if nodes[i] < current_smallest {
                        smallest_even = Some(nodes[i]);
                        smallest_index = Some(i);
                    } else if nodes[i] == current_smallest {
                        // Keep the first occurrence (smaller index)
                    }
                }
            }
        }
        i += 1;
    }
    
    match smallest_even {
        None => {
            assert(forall|j: int| 0 <= j < nodes@.len() ==> nodes@[j] % 2 != 0);
            vec![]
        },
        Some(even_val) => {
            let even_idx = smallest_index.unwrap();
            assert(nodes@[even_idx as int] == even_val);
            assert(even_val % 2 == 0);
            assert(forall|j: int| 0 <= j < nodes@.len() && nodes@[j] % 2 == 0 ==> even_val <= nodes@[j]);
            assert(forall|j: int| 0 <= j < even_idx ==> nodes@[j] % 2 != 0 || nodes@[j] > even_val);
            vec![even_val, even_idx as u32]
        }
    }
}
// </vc-code>

fn main() {}
}
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
    let mut i: u32 = 0;
    let mut smallest_node: u32 = 0;
    let mut smallest_idx: u32 = 0;
    let mut found_even = false;

    while i < nodes.len() as u32
        invariant
            0 <= i <= nodes@.len(),
            nodes@.len() <= u32::MAX,
            found_even <==> (exists|k: int| 0 <= k < i && nodes@[k] % 2 == 0),
            found_even ==> (
                smallest_node % 2 == 0 &&
                forall|k: int| 0 <= k < i && nodes@[k] % 2 == 0 ==> smallest_node <= nodes@[k]
            ),
            found_even ==> (
                0 <= smallest_idx < i &&
                nodes@[smallest_idx as int] == smallest_node &&
                forall|k: int| 0 <= k < smallest_idx ==> nodes@[k] % 2 != 0 || nodes@[k] > smallest_node
            ),
        decreases (nodes.len() as u32) - i
    {
        let current_node = nodes[i as usize];
        if current_node % 2 == 0 {
            if !found_even || current_node < smallest_node {
                smallest_node = current_node;
                smallest_idx = i;
                found_even = true;
            }
        }
        i = i + 1;
    }

    if found_even {
        vec![smallest_node, smallest_idx]
    } else {
        Vec::new()
    }
}
// </vc-code>

}
fn main() {}